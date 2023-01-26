(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list

let max a b = if a > b then a else b
let list_max l = if l = [] then 0 else List.max l

// TODO implement this - DONE
let rec apply_subst (s : subst) (t : ty) : ty =
    let apply = apply_subst s
    match t with
    | TyName(_) -> t
    | TyArrow(dom, codom) -> TyArrow(apply dom,apply codom)
    | TyTuple(tuple) -> TyTuple(List.map (fun x -> apply x ) tuple)
    | TyVar(v) -> 
        let substituted_type_opt = List.tryFind (fun (var, _) -> var = v) s 
        match substituted_type_opt with 
        | Some (_, substituted_type) -> substituted_type
        | None -> t

let apply_subs_on_scheme (s : subst) (Forall (tvs, t)) =
    let relevant_subs = List.filter (fun (tvar, _) -> not (Set.contains tvar tvs)) s
    Forall (tvs, apply_subst relevant_subs t)
        
let apply_subs_on_env (s : subst) (env : scheme env) =
    List.map (fun (vname, sch) -> (vname, apply_subs_on_scheme s sch)) env

let assert_same_variable_diffrent_mapping (subs_list1 : subst) (subs_list2 : subst) =
    let assert_one (tvar, t1) =
        let same_var_sub = List.tryFind (fun (v, _) -> v = tvar) subs_list2
        match (same_var_sub) with
        | None -> ()
        | Some (_, t2) when t1 = t2 -> ()
        | Some (v, t2) -> type_error "type error: inconsistent substitution %s ~~> %s and %s ~~> %s" (pretty_ty (TyVar tvar)) (pretty_ty t1) (pretty_ty (TyVar v)) (pretty_ty t2)
    List.fold (fun _ sub -> assert_one sub) () subs_list1

let assert_argument_is_not_in_sub_result (subs_list : subst) =
    let rec assert_var_appears_in_type (original_type : ty) (var : tyvar) (t : ty) = 
        let assert_rec = List.fold (fun _ ty -> assert_var_appears_in_type original_type var ty) ()
        match t with
        | TyName _ -> ()
        | TyVar v when v <> var -> ()
        | TyArrow (dom, codom) -> assert_rec [dom; codom]
        | TyTuple tys -> assert_rec tys
        | _ -> type_error "type error: found recursive substitution %s ~~> %s" (pretty_ty (TyVar var)) (pretty_ty original_type)
    
    let _ = List.fold (fun _ (var, ty) -> assert_var_appears_in_type ty var ty) () subs_list
    ()

// TODO implement this - DONE (lecture 20)
let compose_subst (subs_list1 : subst) (subs_list2 : subst) : subst =
    let _ = assert_same_variable_diffrent_mapping subs_list1 subs_list2

    let apply_subs1 = apply_subst subs_list1
    let result = List.fold (fun final_subs (var2, t2) -> ((var2, apply_subs1 t2) :: final_subs)) subs_list1 subs_list2
    
    let _ = assert_argument_is_not_in_sub_result result
    result

let rec compose_more_subst (subs: subst list) = List.foldBack (fun s acc -> compose_subst s acc) subs [] 

// TODO implement this
let rec unify (t1 : ty) (t2 : ty) : subst =
    if t1 = t2 then [] else
    match t1, t2 with
    | t, TyVar (v) | TyVar (v), t -> [(v, t)]
    | TyArrow (dom1, codom1), TyArrow (dom2, codom2) -> compose_subst (unify dom1 dom2) (unify codom1 codom2)
    | TyTuple(tup1) , TyTuple(tup2) when List.length tup1 = List.length tup2 
        -> List.fold2 (fun acc it1 it2 -> unify it1 it2 |> compose_subst acc) [] tup1 tup2

    | _ -> type_error "type error: failed to unify type '%s' and '%s'" (pretty_ty t1) (pretty_ty t2)

let rec freevars_ty t =
    match t with
    | TyName s -> Set.empty
    | TyArrow (t1, t2) -> (freevars_ty t1) + (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun r t -> r + freevars_ty t) Set.empty ts

let freevars_scheme (Forall (tvs, t)) = freevars_ty t - tvs

let freevars_scheme_env env =
    List.fold (fun r (_, sch) -> r + freevars_scheme sch) Set.empty env

let gen_sch (env : scheme env) (ty : ty) : scheme =
    let tvs = freevars_ty ty - freevars_scheme_env env
    Forall (tvs, ty)

// type inference
//

let gamma0 = [
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))

]

let rec get_max_var_in_type (t: ty) : tyvar =
    match t with 
    | TyName (_) -> 0
    | TyVar (var) -> var
    | TyArrow (t1,t2) -> max (get_max_var_in_type t1) (get_max_var_in_type t2)
    | TyTuple (tys) -> List.fold (fun acc t -> max acc (get_max_var_in_type t)) 0 tys

let get_max_var_in_scheme (Forall(tvs, t)) = 
    max (list_max (Set.toList tvs)) (get_max_var_in_type t)

let get_max_var_in_env (env: scheme env) = 
    list_max (List.map (fun (_, sch) -> get_max_var_in_scheme sch) env)
    
let get_fresh_tyvar_in (env : scheme env) = TyVar ( 1 + get_max_var_in_env env)

let rec index num = 
    match num with 
    | 0 -> []
    | _ -> (num :: index (num-1))

let rec replace_tyvar (oldv:tyvar) (newv:tyvar) (ty:ty) = 
    let replace = replace_tyvar oldv newv
    match ty with 
    | TyName(_) -> ty
    | TyVar(v) -> if v = oldv then TyVar(newv) else TyVar(oldv)
    | TyArrow(dom, codom) -> TyArrow(replace dom, replace codom)
    | TyTuple(ts) -> TyTuple (List.map (fun t -> replace t) ts)

let instantiate (env: scheme env) (Forall (tsv, t)) =
    let max_var = get_max_var_in_env env
    List.fold2 (fun res tvar idx -> replace_tyvar tvar (tvar + idx) res) t (Set.toList tsv) (index (Set.count tsv))

// TODO for exam
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> TyInt, [] 
    | Lit (LBool _) -> TyBool, []
    | Lit (LFloat _) -> TyFloat, [] 
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, [] 
    | Lit LUnit -> TyUnit, []

    | Var (vname) -> 
        let scho = List.tryFind (fun (n, _) -> n = vname) env
        match scho with
        | None -> get_fresh_tyvar_in env, []
        | Some (_, sch) -> instantiate env sch, []

    | Let (x, tyo, e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let sch = gen_sch env t1
        let t2, s2 = typeinfer_expr ((x, sch) :: env) e2
        let s3 = 
            match tyo with
            | Some ty -> unify ty t2
            | None -> []
        
        apply_subst s3 t2, compose_more_subst [s3;s2;s1]

    | LetRec (f, tyo, lambda, e2) ->
        let extended_env = (f, Forall (Set.empty, get_fresh_tyvar_in env)) :: env
        let t1, s1 = typeinfer_expr extended_env lambda
        let f_sch = gen_sch env t1
        let env_for_e2 = (f, f_sch) :: (apply_subs_on_env s1 env)
        let t2, s2 = typeinfer_expr env_for_e2 e2

        let s3 = 
            match tyo with
            | None -> []
            | Some ty -> unify ty t2
        let final_ty = apply_subst s3 t2

        match final_ty with
        | TyArrow _ -> ()
        | _ -> type_error "type error: expected arrow '%s' to be arrow type but got '%s'" (f) (pretty_ty t2)

        final_ty, compose_more_subst [s3;s2;s1]

    | IfThenElse (e1, e2, e3o) ->
        match e3o with
        | Some e3 -> 
            let t1, s1 = typeinfer_expr env e1
            let s2 = unify t1 TyBool
            let s3 = compose_subst s2 s1
            let t2, s4 = typeinfer_expr (apply_subs_on_env s3 env) e2
            let s5 = compose_subst s4 s3
            let t3, s6 = typeinfer_expr (apply_subs_on_env s5 env) e3
            let s7 = compose_subst s6 s5
            let s8 = unify (apply_subst s7 t2) (apply_subst s7 t3)
            let final_subs = compose_subst s8 s7

            apply_subst final_subs t2, final_subs


        | None -> failwithf "node '%s' is not implemented" (pretty_expr e)

    
    | Lambda (x, tyo, lexpr) ->
        let x_ty = 
            match tyo with 
            | None -> get_fresh_tyvar_in env
            | Some ty -> ty 
        let extended_env = (x, (Forall(Set.empty, x_ty))) :: env
        let codom, final_subs = typeinfer_expr extended_env lexpr
        let dom = apply_subst final_subs x_ty

        TyArrow(dom, codom), final_subs

    | App (e1, e2) -> 
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr (apply_subs_on_env s1 env) e2
        let fresh_var = get_fresh_tyvar_in env
        let s3 = unify t1 (TyArrow (t2, fresh_var))

        apply_subst s3 fresh_var, compose_subst s3 s2

    | Tuple (es) ->
        let fold_func (e : expr) ((types, acc_sub) : (ty list * subst)) = 
            let t, s = typeinfer_expr (apply_subs_on_env acc_sub env) e in ((t::types), compose_subst s acc_sub)
        let (types, final_sub) = List.foldBack fold_func es ([], [])
        TyTuple types, final_sub

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*"), e2) ->
        let t1, _ = typeinfer_expr env e1
        let t2, _ = typeinfer_expr env e2 
        let dom_ty = 
            match t1, t2 with 
            | (TyFloat, _) | (_, TyFloat) -> TyFloat
            | _ -> TyInt
        bin_op dom_ty dom_ty env e1 e2

    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>"), e2) ->
        let t1, _ = typeinfer_expr env e1
        let t2, _ = typeinfer_expr env e2 
        let dom_ty = 
            match t1, t2 with 
            | (TyFloat, _) | (_, TyFloat) -> TyFloat
            | _ -> TyInt
        bin_op dom_ty TyBool env e1 e2

    | BinOp (e1, ("and" | "or"), e2) ->
        bin_op TyBool TyBool env e1 e2

    | _ -> failwithf "node '%s' is not implemented" (pretty_expr e)

and bin_op (dom_type : ty) (codom_type : ty) (env : scheme env) (e1: expr) (e2 : expr) =
    let t1, s1 = typeinfer_expr env e1
    let s2 = unify t1 dom_type
    let t2, s3 = typeinfer_expr (apply_subs_on_env s2 env) e2
    let s4 = unify t2 dom_type
    codom_type, compose_more_subst [s4; s3; s2; s1]




// type checker
//
    
let rec typecheck_expr (env : ty env) (e : expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var x ->
        let _, t = List.find (fun (y, _) -> x = y) env
        t

    | Lambda (x, None, e) -> unexpected_error "typecheck_expr: unannotated lambda is not supported"
    
    | Lambda (x, Some t1, e) ->
        let t2 = typecheck_expr ((x, t1) :: env) e
        TyArrow (t1, t2)

    | App (e1, e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1 with
        | TyArrow (l, r) ->
            if l = t2 then r 
            else type_error "wrong application: argument type %s does not match function domain %s" (pretty_ty t2) (pretty_ty l)
        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)

    | Let (x, tyo, e1, e2) ->
        let t1 = typecheck_expr env e1
        match tyo with
        | None -> ()
        | Some t -> if t <> t1 then type_error "type annotation in let binding of %s is wrong: exptected %s, but got %s" x (pretty_ty t) (pretty_ty t1)
        typecheck_expr ((x, t1) :: env) e2

    | IfThenElse (e1, e2, e3o) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "if condition must be a bool, but got a %s" (pretty_ty t1)
        let t2 = typecheck_expr env e2
        match e3o with
        | None ->
            if t2 <> TyUnit then type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)
            TyUnit
        | Some e3 ->
            let t3 = typecheck_expr env e3
            if t2 <> t3 then type_error "type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" (pretty_ty t2) (pretty_ty t3)
            t2

    | Tuple es ->
        TyTuple (List.map (typecheck_expr env) es)

    | LetRec (f, None, e1, e2) ->
        unexpected_error "typecheck_expr: unannotated let rec is not supported"
        
    | LetRec (f, Some tf, e1, e2) ->
        let env0 = (f, tf) :: env
        let t1 = typecheck_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        typecheck_expr env0 e2

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> TyInt
        | TyFloat, TyFloat -> TyFloat
        | TyInt, TyFloat
        | TyFloat, TyInt -> TyFloat
        | _ -> type_error "binary operator expects two int operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        
    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> ()
        | _ -> type_error "binary operator expects two numeric operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyBool, TyBool -> ()
        | _ -> type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "unary not expects a bool operand, but got %s" (pretty_ty t)
        TyBool
            
    | UnOp ("-", e) ->
        let t = typecheck_expr env e
        match t with
        | TyInt -> TyInt
        | TyFloat -> TyFloat
        | _ -> type_error "unary negation expects a numeric operand, but got %s" (pretty_ty t)

    | UnOp (op, _) -> unexpected_error "typecheck_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
