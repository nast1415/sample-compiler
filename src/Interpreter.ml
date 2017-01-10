
module Expr =
  struct

    open Language.Expr
    open Language.BinOp

    let rec eval state = function
    | Const  n -> n
    | Var    x -> state x
    | Binop  (op, x, y) -> perform_operation op (eval state x) (eval state y)
                      
  end
  
module Stmt =
  struct

    open Language.Stmt

    let eval input stmt =
      let rec eval' ((state, input, output) as c) stmt =
	let state' x = List.assoc x state in
    match stmt with
    | Skip           -> c
    | Seq    (l, r)  -> eval' (eval' c l) r
    | Assign (x, e)  -> ((x, Expr.eval state' e) :: state, input, output)
    | Write   e      -> (state, input, output @ [Expr.eval state' e])
    | Read    x      ->
        let y::input' = input in
        ((x, y) :: state, input', output)
    | If (e, s1, s2) -> if (Expr.eval state' e) <> 0 then (eval' c s1) else (eval' c s2)
    | While (e, s)   -> if (Expr.eval state' e) <> 0 then eval' (eval' c s) stmt else c
               
    in
    let (_, _, result) = eval' ([], input, []) stmt in
    result

  end
