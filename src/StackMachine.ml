type i =
| S_READ
| S_WRITE
| S_PUSH  of int
| S_LD    of string
| S_ST    of string
| S_BINOP of string

module Interpreter =
  struct

    let run input code =
      let rec run' (state, stack, input, output) code =
	match code with
	| []       -> output
	| i::code' ->
	    run'
              (match i with
              | S_READ ->
		  let y::input' = input in
		  (state, y::stack, input', output)
              | S_WRITE ->
		  let y::stack' = stack in
		  (state, stack', input, output @ [y])
              | S_PUSH n ->
		  (state, n::stack, input, output)
              | S_LD x ->
		  (state, (List.assoc x state)::stack, input, output)
              | S_ST x ->
		  let y::stack' = stack in
		  ((x, y)::state, stack', input, output)
              | S_BINOP op ->
		 match op with
                 | "+" ->
                    let y::x::stack' = stack in
                    (state, (x + y)::stack', input, output)
                 | "-" ->
                    let y::x::stack' = stack in
                    (state, (x - y)::stack', input, output)
                 | "*" ->
                    let y::x::stack' = stack in
                    (state, (x * y)::stack', input, output)
                 | "/" ->
                    let y::x::stack' = stack in
                    (state, (x / y)::stack', input, output)
                 | "%" ->
                    let y::x::stack' = stack in
                    (state, (x mod y)::stack', input, output)
                 | "<=" ->
                    let y::x::stack' = stack in
                    (state, (if x <= y then 1 else 0)::stack', input, output)
                 | ">=" ->
                    let y::x::stack' = stack in
                    (state, (if x >= y then 1 else 0)::stack', input, output)
                 | "<" ->
                    let y::x::stack' = stack in
                    (state, (if x < y then 1 else 0)::stack', input, output)
                 | ">" ->
                    let y::x::stack' = stack in
                    (state, (if x > y then 1 else 0)::stack', input, output)
                 | "==" ->
                    let y::x::stack' = stack in
                    (state, (if x == y then 1 else 0)::stack', input, output)
                 | "!=" ->
                    let y::x::stack' = stack in
                    (state, (if x != y then 1 else 0)::stack', input, output)
                 | "&&" ->
                    let y::x::stack' = stack in
                    (state, (if x * y > 0 then 1 else 0)::stack', input, output)
                 | "!!" ->
                    let y::x::stack' = stack in
                    (state, (if x + y > 0 then 1 else 0)::stack', input, output)
              )
              code'
      in
      run' ([], [], input, []) code
	
  end

module Compile =
  struct

    open Language.Expr
    open Language.Stmt

    let rec expr = function
    | Var   x -> [S_LD   x]
    | Const n -> [S_PUSH n]
    | Binop (op, x, y) ->
       match op with
       | "+" ->  expr x @ expr y @ [S_BINOP "+"]
       | "-" ->  expr x @ expr y @ [S_BINOP "-"]
       | "*" ->  expr x @ expr y @ [S_BINOP "*"]
       | "/" ->  expr x @ expr y @ [S_BINOP "/"]
       | "%" ->  expr x @ expr y @ expr x @ expr y @ [S_BINOP "/"; S_BINOP "*"; S_BINOP "-"]
       | "<=" -> expr x @ expr y @ [S_BINOP "<="]
       | ">=" -> expr x @ expr y @ [S_BINOP ">="]
       | "<" ->  expr x @ expr y @ [S_BINOP "<"]
       | ">" ->  expr x @ expr y @ [S_BINOP ">"]
       | "==" -> expr x @ expr y @ [S_BINOP "=="]
       | "!=" -> expr x @ expr y @ [S_BINOP "!="]
       | "&&" ->
          let const_zero = expr @@ Const 0 in
          let const_two  = expr @@ Const 2 in
          const_two @ const_zero @ expr x @ [S_BINOP "<"] @ const_zero @ expr y @ [S_BINOP "<"] @ [S_BINOP "+"] @ [S_BINOP "=="] (* check that 2 == (x > 0) + (y > 0)*)
       | "!!" ->
          let const_zero = expr @@ Const 0 in
          const_zero @ const_zero @ expr x @ [S_BINOP "<"] @ const_zero @ expr y @ [S_BINOP "<"] @ [S_BINOP "+"] @ [S_BINOP "<"] (* check that 0 < (x > 0) + (y > 0)*)
          
       
    let rec stmt = function
    | Skip          -> []
    | Assign (x, e) -> expr e @ [S_ST x]
    | Read    x     -> [S_READ; S_ST x]
    | Write   e     -> expr e @ [S_WRITE]
    | Seq    (l, r) -> stmt l @ stmt r

  end
