type i =
| S_READ
| S_WRITE
| S_PUSH   of int
| S_LD     of string
| S_ST     of string
| S_BINOP  of string
| S_GOTO   of string
| S_IFGOTO of string * string
| S_LABEL  of string

module Interpreter =
  struct

    open Language.BinOp

    let e_to_op = function
      | "z"  -> (==)
      | "nz" -> (!=)
      | _    -> failwith "Stack machine.e_to_op: Unknown parameter"
           
    (* Get instruction pointer for label lbl in the code*)
    let rec find_ip lbl code =
      match code with
      | [] -> failwith "Stack machine.Find ip: Unknown label"
      | i::code' -> if i = S_LABEL lbl then 0 else  1 + find_ip lbl code'

    let run input code =
      let rec run' (state, stack, input, output, ip) code =
        if ip >= (List.length code)
        then output
        else let instruction = (List.nth code ip) in
	    run'
              (match instruction with
              | S_READ ->
		 let y::input' = input in
		 (state, y::stack, input', output, ip + 1)
              | S_WRITE ->
		 let y::stack' = stack in
		 (state, stack', input, output @ [y], ip + 1)
              | S_PUSH n ->
		 (state, n::stack, input, output, ip + 1)
              | S_LD x ->
		 (state, (List.assoc x state)::stack, input, output, ip + 1)
              | S_ST x ->
		 let y::stack' = stack in
		 ((x, y)::state, stack', input, output, ip + 1)
              | S_BINOP op ->
		 let y::x::stack' = stack in
                 (state, (perform_operation op x y)::stack', input, output, ip + 1)
              | S_LABEL lbl ->
                 (state, stack, input, output, ip + 1)
              | S_GOTO  lbl ->
                 (state, stack, input, output, (find_ip lbl code))
              | S_IFGOTO (e, lbl) ->
                 let y::stack' = stack in
                 (state, stack', input, output, if ((e_to_op e) y 0) then (find_ip lbl code) else ip + 1)
              )
 
              code
      in
      run' ([], [], input, [], 0) code
	
  end

module Compile =
  struct

    open Language.Expr
    open Language.Stmt
       

    let rec expr = function
    | Var   x -> [S_LD   x]
    | Const n -> [S_PUSH n]
    | Binop (op, x, y) -> (expr x) @ (expr y) @ [S_BINOP op]

    let i = ref (-1)
    let create_new_lbl () =
      i:= !i + 1;
      string_of_int !i
                                                  
       
    let rec stmt = function
    | Skip               -> []
    | Assign (x, e)      -> expr e @ [S_ST x]
    | Read    x          -> [S_READ; S_ST x]
    | Write   e          -> expr e @ [S_WRITE]
    | Seq    (l, r)      -> stmt l @ stmt r
    | If     (e, s1, s2) ->
       let lbl1 = create_new_lbl () in
       let lbl2 = create_new_lbl () in
       (*let lbl3 = create_new_lbl () in*)
       expr e
       @ [S_IFGOTO ("z", lbl1)]
       @ stmt s1
       @ [S_GOTO lbl2; S_LABEL lbl1]
       @ stmt s2
       @ [S_LABEL lbl2]
    | While   (e, s)     ->
       let lbl1 = create_new_lbl () in
       let lbl2 = create_new_lbl () in
       [S_GOTO lbl2; S_LABEL lbl1]
       @ stmt s
       @ [S_LABEL lbl2]
       @ expr e
       @ [S_IFGOTO ("nz", lbl1)]
                  
  end
