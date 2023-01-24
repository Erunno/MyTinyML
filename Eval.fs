(*
* TinyML
* Eval.fs: evaluator
*)

module TinyML.Eval

open Ast

type opFunction = 
    | NumToNum of (float -> float -> float) * (int -> int -> int)
    | NumToBool of (float -> float -> bool) * (int -> int -> bool)
    | BoolToBool of (bool -> bool -> bool)

let rec eval_expr (env : value env) (e : expr) : value =
    match e with
    | Lit lit -> VLit lit

    | Var x ->
        let _, v = List.find (fun (y, _) -> x = y) env
        v

    | Lambda (x, _, e) -> Closure (env, x, e)

    | App (e1, e2) ->
        let v1 = eval_expr env e1
        let v2 = eval_expr env e2
        match v1 with
        | Closure (env1, x, e) -> eval_expr ((x, v2) :: env1) e
        | RecClosure (env1, f, x, e) -> eval_expr ((x, v2) :: (f, v1) :: env1) e
        | _ -> unexpected_error "eval_expr: non-closure in left side of application: %s" (pretty_value v1)
        
    | IfThenElse (e1, e2, None) ->
        let v1 = eval_expr env e1
        match v1 with
        | VLit (LBool true) -> eval_expr env e2
        | VLit (LBool false) -> VLit LUnit
        | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)
        

    | IfThenElse (e1, e2, Some e3) ->
        let v1 = eval_expr env e1
        eval_expr env (match v1 with
                       | VLit (LBool true) -> e2
                       | VLit (LBool false) -> e3
                       | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)
                       )

    | Let (x, _, e1, e2) -> 
        let v1 = eval_expr env e1
        eval_expr ((x, v1) :: env) e2

    // TODO: test this is ok or fix it - DONE
    | LetRec (f, _, e1, e2) -> 
        let v1 = eval_expr env e1
        match v1 with
        | Closure (venv1, x, e) -> 
            let rec_closure = RecClosure (venv1, f, x, e) 
            in
                eval_expr ((f, rec_closure) :: env) e2
        
        | _ -> unexpected_error "eval_expr: expected closure in rec binding but got: %s" (pretty_value v1)
        // TODO finish this implementation - DONE
    
    // ops DONE
    | UnOp ("not", e1) -> 
        let v = eval_expr env e1 
        in 
            match v with 
            | (VLit (LBool x)) -> VLit (LBool (not x))
            | _ -> unexpected_error "eval_expr: illegal operand in unary operator: %s" (pretty_value v)
    | UnOp ("-", e1) -> 
        let v = eval_expr env e1 
        in 
            match v with 
            | (VLit (LInt x)) -> VLit (LInt (-1 * x))
            | (VLit (LFloat x)) -> VLit (LFloat (-1.0 * x))
            | _ -> unexpected_error "eval_expr: illegal operand in unary operator: %s" (pretty_value v)

    | BinOp (e1, "+", e2) -> binop (NumToNum ((+), (+))) env e1 e2
    | BinOp (e1, "*", e2) -> binop (NumToNum (( * ), ( * ))) env e1 e2
    | BinOp (e1, "-", e2) -> binop (NumToNum ((-), (-))) env e1 e2
    | BinOp (e1, "/", e2) -> binop (NumToNum ((/), (/))) env e1 e2
    | BinOp (e1, "%", e2) -> binop (NumToNum ((%), (%))) env e1 e2
    
    | BinOp (e1, "=", e2) -> binop (NumToBool ((=), (=))) env e1 e2
    | BinOp (e1, ">", e2) -> binop (NumToBool ((>), (>))) env e1 e2
    | BinOp (e1, "<", e2) -> binop (NumToBool ((<), (<))) env e1 e2
    | BinOp (e1, ">=", e2) -> binop (NumToBool ((>=), (>=))) env e1 e2
    | BinOp (e1, "<=", e2) -> binop (NumToBool ((<=), (<=))) env e1 e2
    | BinOp (e1, "<>", e2) -> binop (NumToBool ((<>), (<>))) env e1 e2
    
    | BinOp (e1, "and", e2) -> binop (BoolToBool (&&)) env e1 e2
    | BinOp (e1, "or", e2) -> binop (BoolToBool (||)) env e1 e2
    
    | _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

and binop (op_func: opFunction) (env : value env) (e1 : expr) (e2 : expr) : value = 
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match op_func with
    | NumToNum(op_float, op_int) -> 
        match v1, v2 with
        | VLit (LInt x), VLit (LInt y) -> VLit (LInt (op_int x y))
        | VLit (LFloat x), VLit (LFloat y) -> VLit (LFloat (op_float x y))
        | VLit (LInt x), VLit (LFloat y) -> VLit (LFloat (op_float (float x) y))
        | VLit (LFloat x), VLit (LInt y) -> VLit (LFloat (op_float x (float y)))
        | _ -> unexpected_error "eval_expr: illegal operands in binary operator: %s + %s" (pretty_value v1) (pretty_value v2)
    | NumToBool(op_float, op_int) -> 
        match v1, v2 with
        | VLit (LInt x), VLit (LInt y) -> VLit (LBool (op_int x y))
        | VLit (LFloat x), VLit (LFloat y) -> VLit (LBool (op_float x y))
        | VLit (LInt x), VLit (LFloat y) -> VLit (LBool (op_float (float x) y))
        | VLit (LFloat x), VLit (LInt y) -> VLit (LBool (op_float x (float y)))
        | _ -> unexpected_error "eval_expr: illegal operands in binary operator: %s + %s" (pretty_value v1) (pretty_value v2)
    | BoolToBool(op_bool) -> 
        match v1, v2 with
        | VLit (LBool x), VLit (LBool y) -> VLit (LBool (op_bool x y))
        | _ -> unexpected_error "eval_expr: illegal operands in binary operator: %s + %s" (pretty_value v1) (pretty_value v2)

