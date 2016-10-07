type opnd = R of int | S of int | M of string | L of int

let x86regs = [|
  "%eax"; 
  "%ebx"; 
  "%ecx"; 
  "%edx"; 
  "%esi"; 
  "%edi"
|]

let num_of_regs = Array.length x86regs
let word_size = 4

let eax = R 0
let ebx = R 1
let ecx = R 2
let edx = R 3
let esi = R 4
let edi = R 5

type instr =
| X86Add  of opnd * opnd
| X86Mul  of opnd * opnd
| X86Sub  of opnd * opnd
| X86Div  of opnd * opnd
| X86Mod  of opnd * opnd
| X86Mov  of opnd * opnd
| X86Cmp  of opnd * opnd
| X86Push of opnd
| X86Pop  of opnd
| X86Cdq
| X86Setl
| X86Setle
| X86Setg
| X86Setge
| X86Sete
| X86Setne
| X86Movzbl
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
  | []                              -> R 0
  | (S n)::_                        -> env#allocate (n+1); S (n+1)
  | (R n)::_ when n < num_of_regs-1 -> R (n+1)
  | _                               -> S 0

module Show =
  struct

    let opnd = function
    | R i -> x86regs.(i)
    | S i -> Printf.sprintf "-%d(%%ebp)" (i * word_size)
    | M x -> x
    | L i -> Printf.sprintf "$%d" i

    let instr = function
    | X86Add (s1, s2) -> Printf.sprintf "\taddl\t%s,\t%s"  (opnd s1) (opnd s2)
    | X86Mul (s1, s2) -> Printf.sprintf "\timull\t%s,\t%s" (opnd s1) (opnd s2)
    | X86Sub (s1, s2) -> Printf.sprintf "\tsubl\t%s,\t%s"  (opnd s1) (opnd s2)
    | X86Div (s1, s2) -> Printf.sprintf "\tidivl\t%s"      (opnd s1)
    | X86Mov (s1, s2) -> Printf.sprintf "\tmovl\t%s,\t%s"  (opnd s1) (opnd s2)
    | X86Cmp (s1, s2) -> Printf.sprintf "\tcmp\t%s,\t%s"   (opnd s1) (opnd s2)
    | X86Push s       -> Printf.sprintf "\tpushl\t%s"      (opnd s )
    | X86Pop  s       -> Printf.sprintf "\tpopl\t%s"       (opnd s )
    | X86Setl         -> "\tsetl\t%al"
    | X86Setle        -> "\tsetle\t%al"
    | X86Setg         -> "\tsetg\t%al"
    | X86Setge        -> "\tsetge\t%al"
    | X86Sete         -> "\tsete\t%al"
    | X86Setne        -> "\tsetne\t%al"
    | X86Movzbl       -> "\tmovzbl\t%al,\t%eax"
    | X86Cdq          -> "\tcdq"
    | X86Ret          -> "\tret"
    | X86Call p       -> Printf.sprintf "\tcall\t%s" p

  end

let to_eax x y f =
  match x, y with
  | (S _, S _) -> [X86Push (eax); X86Mov (x, eax)] @ (f eax y) @ [X86Pop (eax)]
  | (_, _) -> (f x y)

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
              | S_READ   -> ([eax], [X86Call "read"])
              | S_WRITE  -> ([], [X86Push (R 0); X86Call "write"; X86Pop (R 0)])
              | S_PUSH n ->
		  let s = allocate env stack in
		  (s::stack, [X86Mov (L n, s)])
              | S_LD x   ->
		  env#local x;
		  let s = allocate env stack in
		  (s::stack, [X86Mov (M x, s)])
              | S_ST x   ->
		  env#local x;
		  let s::stack' = stack in
		  (stack', [X86Mov (s, M x)])
	      | S_BINOP op ->
                 match op with
                 | "+" ->
                    let x::y::stack' = stack in
                    (y::stack', to_eax x y @@ fun x y -> [X86Add (x, y)])
                 | "-" ->
                    let x::y::stack' = stack in
                    (y::stack', to_eax x y @@ fun x y -> [X86Sub (x, y)])
                 | "*" ->
                    let x::y::stack' = stack in
                    (y::stack', to_eax x y @@ fun x y -> [X86Mul (x, y)])
                 | "/" ->
                    let x::y::stack' = stack in
                    (y::stack', [X86Push (eax); X86Push (edx); X86Cdq; X86Mov (y, eax); X86Div (x, y); X86Mov (eax, y); X86Pop (edx); X86Pop (eax)])
                 | "%" ->
                    let x::y::stack' = stack in
                    (y::stack', [X86Push (eax); X86Push (edx); X86Cdq; X86Mov (y, eax); X86Div (x, y); X86Mov (edx, y); X86Pop (edx); X86Pop (eax)])
                 | "<" ->
                    let x::y::stack' = stack in
                    (y::stack', to_eax x y @@ fun x y -> [X86Push eax; X86Cmp (x, y); X86Setl; X86Movzbl; X86Mov (eax, y); X86Pop (eax)])
                 | "<=" ->
                    let x::y::stack' = stack in
                    (y::stack', to_eax x y @@ fun x y -> [X86Push eax; X86Cmp (x, y); X86Setle; X86Movzbl; X86Mov (eax, y); X86Pop (eax)])
                 | ">" ->
                    let x::y::stack' = stack in
                    (y::stack', to_eax x y @@ fun x y -> [X86Push eax; X86Cmp (x, y); X86Setg; X86Movzbl; X86Mov (eax, y); X86Pop (eax)])
                 | ">=" ->
                    let x::y::stack' = stack in
                    (y::stack', to_eax x y @@ fun x y -> [X86Push eax; X86Cmp (x, y); X86Setge; X86Movzbl; X86Mov (eax, y); X86Pop (eax)])
                 | "==" ->
                    let x::y::stack' = stack in
                    (y::stack', to_eax x y @@ fun x y -> [X86Push eax; X86Cmp (x, y); X86Sete; X86Movzbl; X86Mov (eax, y); X86Pop (eax)])
                 | "!=" ->
                    let x::y::stack' = stack in
                    (y::stack', to_eax x y @@ fun x y -> [X86Push eax; X86Cmp (x, y); X86Setne; X86Movzbl; X86Mov (eax, y); X86Pop (eax)])
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
  ignore (Sys.command (Printf.sprintf "gcc -m32 -o %s ../runtime/runtime.o %s.s" name name))
