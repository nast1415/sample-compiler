type opnd = R of int | SR of int | S of int | M of string | L of int

let x86regs = [|
  "%eax"; 
  "%edx"; 
  "%ecx"; 
  "%ebx"; 
  "%esi"; 
  "%edi"
|]

let x86small = [|
  "%al";
  "%ah";
  "%dl";
  "%dh"
|]

let num_of_regs = Array.length x86regs
let word_size = 4

let eax = R 0
let edx = R 1
let ecx = R 2
let ebx = R 3
let esi = R 4
let edi = R 5

let al = SR 0
let ah = SR 1
let dl = SR 2
let dh = SR 3

type instr =
| X86Add  of opnd * opnd
| X86Mul  of opnd * opnd
| X86Sub  of opnd * opnd
| X86Div  of opnd * opnd
| X86Mod  of opnd * opnd
| X86Mov  of opnd * opnd
| X86Cmp  of opnd * opnd
| X86Xor  of opnd * opnd
| X86Or   of opnd * opnd
| X86And  of opnd * opnd
| X86Push of opnd
| X86Pop  of opnd
| X86Cdq
| X86Lbl    of string
| X86Goto   of string
| X86Ifgoto of string * string
| X86Set    of string * opnd
| X86Ret
| X86Call of string


module S = Set.Make (String)

class x86env =
  object(self)
    val    local_vars = ref S.empty
    method local x    = local_vars := S.add x !local_vars
    method local_vars = S.elements !local_vars

    val    allocated  = ref 0
    method allocate n = allocated := max n !allocated
    method allocated  = !allocated
  end

let allocate env stack =
  match stack with
  | []                              -> R 2
  | (S n)::_                        -> env#allocate (n+2); S (n+1)
  | (R n)::_ when n < num_of_regs-1 -> R (n+1)
  | _                               -> env#allocate (1); S 0

module Show =
  struct

    let opnd = function
    | R i  -> x86regs.(i)
    | SR i -> x86small.(i)
    | S i  -> Printf.sprintf "-%d(%%ebp)" (i * word_size)
    | M x  -> x
    | L i  -> Printf.sprintf "$%d" i

    let comp op = match op with
    | "<"  -> "l"
    | "<=" -> "le"
    | ">"  -> "g"
    | ">=" -> "ge"
    | "!=" -> "ne"
    | "==" -> "e"
    | _    -> op

    let instr = function
    | X86Add (s1, s2) -> Printf.sprintf "\taddl\t%s,\t%s"  (opnd s1) (opnd s2)
    | X86Mul (s1, s2) -> Printf.sprintf "\timull\t%s,\t%s" (opnd s1) (opnd s2)
    | X86Sub (s1, s2) -> Printf.sprintf "\tsubl\t%s,\t%s"  (opnd s1) (opnd s2)
    | X86Div (s1, s2) -> Printf.sprintf "\tidivl\t%s"      (opnd s1)

    | X86Mov (s1, s2) -> Printf.sprintf "\tmovl\t%s,\t%s"  (opnd s1) (opnd s2)
    | X86Cmp (s1, s2) -> Printf.sprintf "\tcmp\t%s,\t%s"   (opnd s1) (opnd s2)
    | X86Push s       -> Printf.sprintf "\tpushl\t%s"      (opnd s )
    | X86Pop  s       -> Printf.sprintf "\tpopl\t%s"       (opnd s )

    | X86Xor (s1, s2) -> Printf.sprintf "\txorl\t%s,\t%s"  (opnd s1) (opnd s2)
    | X86Or  (s1, s2) -> Printf.sprintf "\torl\t%s,\t%s"   (opnd s1) (opnd s2)
    | X86And (s1, s2) -> Printf.sprintf "\tandl\t%s,\t%s"  (opnd s1) (opnd s2)
    | X86Set (s1, s2) -> Printf.sprintf "\tset%s\t%s"     (comp s1) (opnd s2)

    | X86Lbl s         -> Printf.sprintf "label%s:" s
    | X86Goto s        -> Printf.sprintf "\tjmp\tlabel%s" s
    | X86Ifgoto (e, s) -> Printf.sprintf "\tj%s\tlabel%s" e s

    | X86Cdq          -> "\tcdq"
    | X86Ret          -> "\tret"
    | X86Call p       -> Printf.sprintf "\tcall\t%s" p

  end
    

module Compile =
  struct

    open StackMachine

    let stack_program env code =
      let rec compile stack code =
	match code with
	| []       -> []
	| i::code' ->
	    let (stack', x86code) =
              match i with
              | S_READ   -> ([R 2], [X86Call "read"; X86Mov (eax, R 2)])
              | S_WRITE  -> ([], [X86Push (R 2); X86Call "write"; X86Pop (R 2)])
              | S_PUSH n ->
		              let s = allocate env stack in
		              (s::stack, [X86Mov (L n, s)])
              | S_LD x   ->
            		  env#local x;
            		  let s = allocate env stack in
                    (match s with
                    | S _ -> (s::stack, [X86Mov (M x, eax); X86Mov (eax, s)])
                    | _   -> (s::stack, [X86Mov (M x, s)]))
              | S_ST x   ->
            		  env#local x;
            		  let s::stack' = stack in
              		  (match s with
                      | S _ -> (stack', [X86Mov (s, eax); X86Mov (eax, M x)])
                      | _   -> (stack', [X86Mov (s, M x)]))
              | S_LABEL lbl ->
                  (stack, [X86Lbl lbl])
              | S_GOTO lbl ->
                  (stack, [X86Goto lbl])
              | S_IFGOTO (e, lbl) ->
                  let y::stack' = stack in
                  (stack', [X86Cmp (L 0, y); X86Ifgoto (e, lbl)])
	            | S_BINOP op ->
                  match op with
                  | "+" ->
                    let x::y::stack' = stack in
                    (y::stack', [X86Mov (y, eax); X86Add (x, eax); X86Mov (eax, y)])
                  | "-" ->
                    let x::y::stack' = stack in
                    (y::stack', [X86Mov (y, eax); X86Sub (x, eax); X86Mov (eax, y)])
                  | "*" ->
                    let x::y::stack' = stack in
                    (y::stack', [X86Mov (y, eax); X86Mul (x, eax); X86Mov (eax, y)])
                  | "/" ->
                    let x::y::stack' = stack in
                    (y::stack', [X86Mov (y, eax); X86Cdq; X86Div (x, y); X86Mov (eax, y)])
                  | "%" ->
                    let x::y::stack' = stack in
                    (y::stack', [X86Mov (y, eax); X86Cdq; X86Div (x, y); X86Mov (edx, y)])
                  | "<" | "<=" | ">" | ">=" | "!=" | "==" ->
                    let x::y::stack' = stack in
                    (y::stack', [X86Mov (y, edx); X86Xor (eax, eax); X86Cmp (x, edx); X86Set (op, al); X86Mov (eax, y)])
                  | "&&" ->
                    let x::y::stack' = stack in
                    (y::stack', [
                      (* 
                        Set eax value to null, mov x to edx, check that edx is not null
                        if it is true - in eax we now have not null 
                      *)
                      X86Xor (eax, eax);
                      X86Mov (x, edx);
                      X86Cmp (edx, eax);
                      X86Set ("ne", al);
                      (* 
                        Mov y to edx and mul eax and edx (result in edx)
                        result of && is not null only if eax not null (x != 0) and edx not null (y != 0) 
                      *)
                      X86Mov (y, edx);
                      X86Mul (eax, edx);
                      X86Xor (eax, eax);
                      X86Cmp (edx, eax);
                      X86Set ("ne", al);
                      X86Mov (eax, y)])
                  | "!!" ->
                    let x::y::stack' = stack in
                    (y::stack', [
                      (* Set eax value to null, mov x to edx, check that or y, edx not null*)
                      X86Xor (eax, eax);
                      X86Mov (x, edx);
                      X86Or (y, edx);
                      X86Cmp (edx, eax);
                      X86Set ("ne", al);
                      X86Mov (eax, y)])
               
	    in
	    x86code @ compile stack' code'
      in
      compile [] code

  end

let compile stmt =
  let env = new x86env in
  let code = Compile.stack_program env @@ StackMachine.Compile.stmt stmt in
  let asm  = Buffer.create 1024 in
  let (!!) s = Buffer.add_string asm s in
  let (!)  s = !!s; !!"\n" in
  !"\t.text";
  List.iter (fun x ->
      !(Printf.sprintf "\t.comm\t%s,\t%d,\t%d" x word_size word_size))
    env#local_vars;
  !"\t.globl\tmain";
  let prologue, epilogue =
    if env#allocated = 0
    then (fun () -> ()), (fun () -> ())
    else
      (fun () ->
         !"\tpushl\t%ebp";
         !"\tmovl\t%esp,\t%ebp";
         !(Printf.sprintf "\tsubl\t$%d,\t%%esp" (env#allocated * word_size))
      ),
      (fun () ->
         !"\tmovl\t%ebp,\t%esp";
         !"\tpopl\t%ebp"
      )
  in
  !"main:";
  prologue();
  List.iter (fun i -> !(Show.instr i)) code;
  epilogue();
  !"\txorl\t%eax,\t%eax";
  !"\tret";
  Buffer.contents asm

let build stmt name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (compile stmt);
  close_out outf;
  ignore (Sys.command (Printf.sprintf "gcc -m32 -o %s $RC_RUNTIME/runtime.o %s.s" name name))
