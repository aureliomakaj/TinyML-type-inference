﻿(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list


let rec freevars_ty (t : ty) : tyvar Set =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts
    | TyQuant (Forall (l, t)) -> Set.ofList l

let freevars_scheme (Forall (tvs, t)) =
    Set.difference (freevars_ty t) (Set.ofList tvs)

//Given a type and a list of subsitutions, returns the type substituted.
let rec apply_subst (t : ty) (s : subst) : ty = 
    match t with
    //For type names there is no substitution
    | TyName _ -> t
    //For type variables, if there is a substitution, give the substituted type, 
    //otherwise return the type variable
    | TyVar t1 -> 
        let elem = List.tryFind (fun (tyvar, ty) -> tyvar = t1) s
        match elem with 
        | None -> t
        | Some (_, t2) -> t2
    //For arrow types, apply the substitution on the domain and on the codomain
    | TyArrow (td, tc) -> TyArrow((apply_subst td s), (apply_subst tc s))
    //For tuples, apply the substitution on each element of the tuple
    | TyTuple tup -> TyTuple (List.map (fun t -> apply_subst t s) tup)

    | TyQuant (Forall (l, tt)) -> 
        t


(*let rec mapFilter f l =
    match l with 
    | [] -> []
    | x :: xs -> 
        let mapped = f x
        match mapped with
        | None -> [] @ mapFilter f xs
        | Some _ -> x :: (mapFilter f xs)
*)




//Unification function (Martelli-Montanari)
let rec unify (t1 : ty) (t2 : ty) : subst = 
    match t1, t2 with

    | TyName _, TyName _ ->
        if t1 <> t2 
            then type_error "unification_error: typed names %s and %s must be of the same type to be unified " (pretty_ty t1) (pretty_ty t2) 
            else []
    | TyVar _, TyVar _ -> []

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

    | TyTuple tup1, TyTuple tup2 ->
        if tup1.Length <> tup2.Length 
            then type_error "Unification error: unification of tuples with different lengths. Got %d and %d" tup1.Length tup2.Length

        let rec check_tuples l1 l2 = 
            match l1, l2 with 
            | [], [] -> []
            | x::xs, y::ys -> (unify x y) @ (check_tuples xs ys)
            | _ -> []

        check_tuples tup1 tup2

    | TyQuant (Forall (l, t)), _ -> 
        unify t t2  
    | _ -> type_error "Unification error: unsupported unification"

(*
Composition of two substitutions: 
we start to iterate the first list and check if the element is also in the second:
- if there is, we try to unify the two types. 
    - if there is a substitution we use it and discard the other two
    - if not, use the first and discard the other.
- if there isn't, save it and continue with the iteration
*)
and compose_subst (s1 : subst) (s2 : subst) : subst = 
    let rec f acc (l1, l2) = 
        acc @ 
            match l1 with 
            | [] -> l2
            | (tyvar, ty) :: xs ->   
                let elem = List.tryFind (fun (x0, _) -> tyvar = x0) l2
                match elem with 
                | None -> (tyvar, ty) :: (f acc (xs, l2))
                | Some (_, new_ty) -> 
                    let subs = unify ty new_ty
                    //Remove the element already checked from the second list
                    let filtered = List.filter (fun (a, b) -> a <> tyvar && b <> new_ty) l2
                    if List.isEmpty subs
                        then (tyvar, ty) :: filtered
                        else subs @ filtered
        
                
    f [] (s1, s2)

//Generate an unused integer to be used of a fresh type variable
let next_tyvar env = 
    let res = List.ofSeq (List.fold (fun set (_, ty) -> Set.union set (freevars_ty ty)) Set.empty env)
    match res with
    | [] -> 1
    | _ -> List.max(res) + 1

let rec freevars_env (env : ty env) = 
    match env with
    | [] -> Set.empty
    | (s, v) :: xs -> 
        match v with 
        | TyQuant (Forall (l, ty)) -> Set.union (freevars_ty v) (freevars_env xs)
        | _ -> freevars_env xs
let rec typeinfer_expr (env : ty env) (e : expr) : ty * subst =
    match e with
    //Literals are already type names
    | Lit (LInt _) -> (TyInt, [])
    | Lit (LFloat _) -> (TyFloat, [])
    | Lit (LString _) -> (TyString, [])
    | Lit (LChar _) -> (TyChar, [])
    | Lit (LBool _) -> (TyBool, [])
    | Lit LUnit -> (TyUnit, [])
    
    //For variables, just look if the variable is in the environment
    | Var x ->
        try
            let _, t = List.find (fun (y, _) -> x = y) env
            (t, [])
        with
        | :? System.Collections.Generic.KeyNotFoundException -> type_error "Unknown identifier '%s'" x

    | Lambda (x, None, e) -> 
        let t1 = TyVar (next_tyvar env) //new fresh type variable
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
            //the possibile substitutions found from the two expressions
            let composed_subst = (
                try
                    //Unify the domain with the type of the expression
                    compose_subst (compose_subst s1 s2) (unify l t2)
                with
                | TypeError _ -> type_error "the domain of the function is %s, but got %s" (pretty_ty l) (pretty_ty t2)
            )
            (apply_subst r composed_subst, composed_subst)

        //If t1 is unknown, we suppose that has type 'a -> 'b, and try to understand more about 'a and 'b from expression e2
        | TyVar tt1 ->
            let t2, s2 = typeinfer_expr env e2
            let free_vars = Set.union (freevars_ty t2) (Set.singleton tt1)
            let n = if Set.count free_vars > 0 then (Set.maxElement free_vars) + 1 else 1
            let n1 = max (next_tyvar env) n
            //let n = next_tyvar env
            let codomain = TyVar n1 //fresh type variable
            let composed = compose_subst s1 s2 //compose substitutions from the expressions
            let arr = TyArrow (t2, codomain)
            let composed2 = compose_subst composed (unify t1 arr)
            (apply_subst codomain composed2, composed2)

        //If we have a quantification, we don't have to substitute, because the type variables are generalized.
        //Just check if the domain with the result of the second expression are unifiable
        | TyQuant (Forall (l, ty)) -> 
            match ty with 
            | TyArrow (dom, cod) -> 
                let t2, s2 = typeinfer_expr env e2

                //let diff = freevars_scheme (Forall (l, ty))
                let composed = (
                    try
                        compose_subst ( compose_subst s1 s2 ) (unify dom t2)
                    with
                    | TypeError _ -> type_error "the domain of the function is %s, but got %s" (pretty_ty dom) (pretty_ty t2)
                )

                //let filtered = List.filter (fun (var, _) -> Set.contains var diff ) composed 

                (apply_subst cod composed, composed)
            | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty ty)

        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)
    
    //let-polymorphism. 
    | Let (x, None, e1, e2) -> 
        let t1, s = typeinfer_expr env e1
        let free_vars = freevars_ty t1
        let x_ty = TyQuant (Forall (List.ofSeq free_vars, t1))
        let t2, s2 = typeinfer_expr ((x, x_ty)::env) e2
        ((apply_subst t2 s2), compose_subst s s2)

    | Let (x, Some t, e1, e2) ->
        let env0 = (x, t)::env
        let t1, s = typeinfer_expr env0 e1
        if t1 <> t then type_error "Expected type for '%s' is %s, got %s" x (pretty_ty t) (pretty_ty t1) 
        let t2, s2 = typeinfer_expr env0 e2
        (t2, compose_subst s s2)

    | LetRec (f, None, e1, e2) ->
        //The unknown type before the inference of e1
        let n = next_tyvar env
        let pre_dom = TyVar n
        let pre_cod = TyVar (n + 1)
        let pre_arr = TyArrow (pre_dom, pre_cod)
        let pre_free_vars = freevars_ty pre_arr
        let pre_ty = (TyQuant (Forall (List.ofSeq pre_free_vars, pre_arr)))
        let env0 = (f, pre_ty) :: env
        let t1, s = typeinfer_expr env0 e1
        //New info after the type inference of the expression
        let post_dom = apply_subst pre_dom s
        let post_cod = apply_subst pre_cod s
        let post_arr = TyArrow (post_dom, post_cod)
        let post_free_vars = freevars_ty post_arr
        let post_ty = (TyQuant (Forall (List.ofSeq post_free_vars, post_arr)))
        let t2, s2 = typeinfer_expr ((f, post_ty)::env) e2
        (t2, compose_subst s s2)

    | LetRec (f, Some tf, e1, e2) ->
        let env0 = (f, tf) :: env
        let t1, s1 = typeinfer_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        let t2, s2 = typeinfer_expr env0 e2
        (t2, compose_subst s1 s2)
    
    //For tuples, we must iterate through all the expressions in the tuple, collect
    //the substitutions and use it to check if the following expressions are respecting the 
    //previous ones
    | Tuple tup ->
        let f_env = freevars_env env
        //Function for the mapFold
        let mapAndFold acc elem = 
            let t, s = typeinfer_expr env elem
            let filtered = List.filter (fun (tvar, _) -> not (Set.contains tvar f_env) ) s
            (t, compose_subst acc filtered)

        let expressions, composed_subst = List.mapFold mapAndFold [] tup

        (apply_subst (TyTuple expressions) composed_subst, composed_subst)


    | IfThenElse (e1, e2, e3o) ->
        let t1, s1 = typeinfer_expr env e1
        if t1 <> TyBool then type_error "if condition must be a bool, but got a %s" (pretty_ty t1)
        let t2, s2 = typeinfer_expr env e2
        let composed = compose_subst s1 s2
        match e3o with
        | None ->
            if t2 <> TyUnit then type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)
            (TyUnit, composed)
        | Some e3 ->
            let t3, s3 = typeinfer_expr env e3
            let com = compose_subst composed s3
            let com2 = compose_subst com (unify t2 t3)
            (apply_subst t2 com2, com2)

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*"  as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr env e2
        let composed_subst = (
            try
                compose_subst (compose_subst s1 s2) (unify t1 t2)
            with
            | TypeError _ -> type_error "binary operator expects two numeric types, but got %s and %s" (pretty_ty t1) (pretty_ty t2)
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
            | TypeError _ -> type_error "binary operator expects two numeric types, but got %s and %s" (pretty_ty t1)  (pretty_ty t2)
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
            | TypeError _ -> type_error "logical binary operator expects two bools operands, but got %s and %s" (pretty_ty t1) (pretty_ty t2)
        )
        match t1, t2 with
        | TyBool, TyBool 
        | TyBool, TyVar _
        | TyVar _, TyBool -> (TyBool, composed_subst)
        | _ -> type_error "binary operator expects two bools operands, but got %s and %s" (pretty_ty t1) (pretty_ty t2)   
    
    | BinOp (_, op, _) -> unexpected_error "unsupported binary operator (%s)" op
    
    | UnOp ("not", e) ->
        let t, s = typeinfer_expr env e
        if t <> TyBool then type_error "unary operator 'not' expects a bool operand, but got %s" (pretty_ty t)
        (TyBool, s)
                
    | UnOp ("-", e) ->
        let t, s = typeinfer_expr env e
        match t with
        | TyInt -> (TyInt, s)
        | TyFloat -> (TyFloat, s)
        | _ -> type_error "unary operator 'negation' expects a numeric operand, but got %s" (pretty_ty t)
    
    | UnOp (op, _) -> unexpected_error "unsupported unary operator (%s)" op

    | _ -> unexpected_error "typeinfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

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
