(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list

// TODO implement this
let rec apply_subst (t : ty) (s : subst) : ty = 
    match t with
    | TyName _ -> t
    | TyVar t1 -> 
        let elem = List.tryFind (fun (tyvar, ty) -> tyvar = t1) s
        match elem with 
        | None -> t
        | Some (_, t2) -> t2

    | TyArrow (td, tc) -> TyArrow((apply_subst td s), (apply_subst tc s))
    | TyTuple tup -> TyTuple (List.map (fun t -> apply_subst t s) tup)

// TODO implement this
let compose_subst (s1 : subst) (s2 : subst) : subst = s1 @ s2

let rec freevars_ty (t : ty) : tyvar Set =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts 

let freevars_scheme (Forall (tvs, t)) =
    Set.difference (freevars_ty t) (Set.ofList tvs)

// TODO implement this
let rec unify (t1 : ty) (t2 : ty) : subst = 
    match t1, t2 with
    | TyName _, TyName _ ->
        if t1 <> t2 
            then type_error "unification_error: typed names %s and %s must be of the same type to be unified " (pretty_ty t1) (pretty_ty t2) 
            else []
    | TyVar t , _  -> 
        let free_vars = freevars_ty t2
        if Set.contains t free_vars 
            then type_error "Unification error: recursion detected"
            else [(t, t2)]

    | _, TyVar t -> 
        let free_vars = freevars_ty t1
        if Set.contains t free_vars 
            then type_error "Unification error: recursion detected"
            else [(t, t1)]

    | TyArrow (tt1, tt2) , TyArrow (tt3, tt4) -> compose_subst (unify tt1 tt3) ( unify tt2 tt4)
    | _ -> type_error "Unification error: unsupported unification"



// type inference
//
let gamma0 = [
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
]

let next_tyvar (env : ty env) : ty = 
    let res = List.ofSeq (List.fold (fun set (_, ty) -> Set.union set (freevars_ty ty)) Set.empty env)
    TyVar (
        match res with
        | [] -> 1
        | _ -> List.max(res) + 1
    )

let rec typeinfer_expr (env : ty env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> (TyInt, [])
    | Lit (LFloat _) -> (TyFloat, [])
    | Lit (LString _) -> (TyString, [])
    | Lit (LChar _) -> (TyChar, [])
    | Lit (LBool _) -> (TyBool, [])
    | Lit LUnit -> (TyUnit, [])
    
    | Var x ->
        try
            let _, t = List.find (fun (y, _) -> x = y) env
            (t, [])
        with
        | :? System.Collections.Generic.KeyNotFoundException -> type_error "Unknown identifier '%s'" x

    | Lambda (x, None, e) -> 
        let t1 = next_tyvar env
        let t2, s = typeinfer_expr ((x, t1) :: env) e
        (TyArrow (apply_subst t1 s, t2), s)
    
    | Lambda (x, Some t1, e) -> 
        let t2, subst = typeinfer_expr ((x, t1) :: env) e
        (TyArrow (t1, t2), subst)
    
    | App (e1, e2) -> 
        let t1, s1= typeinfer_expr env e1
        match t1 with 
        | TyArrow (l, r) -> 
            let t2, s2 = typeinfer_expr env e2
            let composed_subst = (
                try
                    compose_subst (compose_subst s1 s2) (unify l t2)
                with
                | TypeError _ -> type_error "the domain of the function is %s, but got %s" (pretty_ty l) (pretty_ty t2)
            )
            (apply_subst r composed_subst, composed_subst)
        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)
    
    | Let (x, None, e1, e2) -> 
        let t1, s = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr ((x, t1)::env) e2
        ((apply_subst t2 s2), compose_subst s s2)

    //| Let (x, Some t, e1, e2) -> 
    //    let v1 = eval_expr env e1
    //    eval_expr ((x, v1) :: env) e2
    //| App (e1, e2) ->
    //    let t1, s1= typeinfer_expr env e1
    //    let t2, s2 = typeinfer_expr env e2
    //    match t1 with
    //    | TyArrow (l, r) ->
    //        if l = t2 then r 
    //        else type_error "wrong application: argums does not match function domainent type % %s" (pretty_ty t2) (pretty_ty l)
    //    | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)
    
    | BinOp (e1, ("+" | "-" | "/" | "%" | "*"  as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr env e2
        let composed_subst = (
            try
                compose_subst (compose_subst s1 s2) (unify t1 t2)
            with
            | TypeError _ -> type_error "binary operator expects operands with same type name, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        )
        match t1, t2 with
        | TyInt, TyInt
        | TyInt, TyVar _
        | TyVar _, TyInt -> (TyInt, composed_subst)
        | TyVar _, TyVar _ ->
            let compose = compose_subst (unify t1 TyInt) (unify t2 TyInt)
            (TyInt, compose_subst composed_subst compose)
        | TyFloat, TyFloat
        | TyFloat, TyVar _
        | TyVar _, TyFloat -> (TyFloat, composed_subst)
        | _ -> type_error "Unsupported types for binary operation. Expected int or float, got %s and %s" (pretty_ty t1) (pretty_ty t2)

    | BinOp (e1, ( "<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr env e2
        let composed_subst = (
            try
                compose_subst (compose_subst s1 s2) (unify t1 t2)
            with
            | TypeError _ -> type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        )
        match t1, t2 with
        | TyInt, TyInt
        | TyInt, TyVar _
        | TyVar _, TyInt
        | TyFloat, TyFloat
        | TyFloat, TyVar _
        | TyVar _, TyFloat -> (TyBool, composed_subst)
        | _ -> type_error "Unsupported types for binary operation. Expected int or float, got %s and %s" (pretty_ty t1) (pretty_ty t2)

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr env e2
        let composed_subst = (
            try
                compose_subst (compose_subst s1 s2) (unify t1 t2)
            with
            | TypeError _ -> type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        )
        match t1, t2 with
        | TyBool, TyBool 
        | TyBool, TyVar _
        | TyVar _, TyBool -> (TyBool, composed_subst)
        | _ -> type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)   
    
    | _ -> failwith "not implemented"


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
            else type_error "wrong application: argums does not match function domainent type % %s" (pretty_ty t2) (pretty_ty l)
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
