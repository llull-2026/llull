module IntMap = Map.Make(Int)
module IntSet = Set.Make(Int)

type typ =
    | Int
    | Unit
    | ListInt
    | TVar of int
    | TyVar of int
    | Arrow of typ * typ
    | Forall of typ
    | Ref of typ

type type_eq = typ * typ

type const =
    | CInt of int
    | CUnit
    | CNil
    | CCons
    | CHd
    | CTl
    | CPlus

type term =
    | Var of int
    | Lam of typ * term
    | App of term * term
    | Const of const
    | TyLam of term
    | TyApp of term * typ
    | MkRef of term
    | Deref of term
    | Assign of term * term
    | Seq of term * term
    | Minus of term * term
    | Ifz of term * term * term

type var_binding = {
    sym_id : int;
    de_bruijn_idx : int;
    binding_type : typ;
}

type fact = {
    term : term;
    typ : typ;
    bindings : var_binding list;
}

let string_of_const = function
    | CInt n -> string_of_int n
    | CUnit -> "()"
    | CNil -> "nil"
    | CCons -> "cons"
    | CHd -> "hd"
    | CTl -> "tl"
    | CPlus -> "+"

let rec string_of_typ t =
    match t with
    | Int -> "int"
    | Unit -> "unit"
    | ListInt -> "(list int)"
    | TVar i -> "a" ^ string_of_int i
    | TyVar i -> "T" ^ string_of_int i
    | Arrow (t1, t2) ->
        let s1 = match t1 with
            | Arrow _ | Forall _ -> "(" ^ string_of_typ t1 ^ ")"
            | _ -> string_of_typ t1 in
        s1 ^ " -> " ^ string_of_typ t2
    | Forall body -> "(forall. " ^ string_of_typ body ^ ")"
    | Ref t ->
        let inner = match t with
            | Arrow _ | Forall _ -> "(" ^ string_of_typ t ^ ")"
            | _ -> string_of_typ t in
        "ref " ^ inner

let rec string_of_term t =
    match t with
    | Var i -> "#" ^ string_of_int i
    | Lam (ty, body) -> "lam[" ^ string_of_typ ty ^ "]." ^ string_of_term body
    | App (t1, t2) ->
        let s1 = match t1 with
            | Lam _ | TyLam _ -> "(" ^ string_of_term t1 ^ ")"
            | _ -> string_of_term t1 in
        let s2 = match t2 with
            | App _ | Lam _ | TyLam _ -> "(" ^ string_of_term t2 ^ ")"
            | _ -> string_of_term t2 in
        s1 ^ " " ^ s2
    | Const c -> string_of_const c
    | TyLam body -> "Lam_T." ^ string_of_term body
    | TyApp (e, ty) -> string_of_term e ^ "[" ^ string_of_typ ty ^ "]"
    | MkRef e -> "ref " ^ paren_atom e
    | Deref e -> "!" ^ paren_atom e
    | Assign (e1, e2) -> paren_atom e1 ^ " := " ^ paren_atom e2
    | Seq (e1, e2) -> string_of_term e1 ^ "; " ^ string_of_term e2
    | Minus (e1, e2) -> paren_arith e1 ^ " - " ^ paren_atom e2
    | Ifz (e1, e2, e3) ->
        "ifz " ^ string_of_term e1 ^ " then " ^ string_of_term e2 ^
        " else " ^ string_of_term e3

and paren_atom t =
    match t with
    | Var _ | Const _ -> string_of_term t
    | _ -> "(" ^ string_of_term t ^ ")"

and paren_arith t =
    match t with
    | Var _ | Const _ | Minus _ -> string_of_term t
    | _ -> "(" ^ string_of_term t ^ ")"

let string_of_fact f =
    string_of_term f.term ^ " : " ^ string_of_typ f.typ

let fact_type_string f = string_of_typ f.typ

let rec term_subterms t =
    let self = string_of_term t in
    match t with
    | Var _ | Const _ -> [self]
    | Lam (_, body) | TyLam body | MkRef body | Deref body ->
        self :: term_subterms body
    | TyApp (e, _) -> self :: term_subterms e
    | App (e1, e2) | Assign (e1, e2) | Seq (e1, e2) | Minus (e1, e2) ->
        self :: term_subterms e1 @ term_subterms e2
    | Ifz (e1, e2, e3) ->
        self :: term_subterms e1 @ term_subterms e2 @ term_subterms e3

let fact_subterm_strings f = term_subterms f.term

let rec shift_tyvar cutoff offset t =
    match t with
    | Int | Unit | ListInt | TVar _ -> t
    | TyVar i -> if i >= cutoff then TyVar (i + offset) else t
    | Arrow (t1, t2) -> Arrow (shift_tyvar cutoff offset t1, shift_tyvar cutoff offset t2)
    | Forall body -> Forall (shift_tyvar (cutoff + 1) offset body)
    | Ref t -> Ref (shift_tyvar cutoff offset t)

let rec subst_tyvar_at depth replacement t =
    match t with
    | Int | Unit | ListInt | TVar _ -> t
    | TyVar i ->
        if i = depth then shift_tyvar 0 depth replacement
        else if i > depth then TyVar (i - 1)
        else t
    | Arrow (t1, t2) ->
        Arrow (subst_tyvar_at depth replacement t1, subst_tyvar_at depth replacement t2)
    | Forall body -> Forall (subst_tyvar_at (depth + 1) replacement body)
    | Ref t -> Ref (subst_tyvar_at depth replacement t)

let subst_tyvar replacement t = subst_tyvar_at 0 replacement t

let const_type_of = function
    | CInt _ -> Int
    | CUnit -> Unit
    | CNil -> ListInt
    | CCons -> Arrow (Int, Arrow (ListInt, ListInt))
    | CHd -> Arrow (ListInt, Int)
    | CTl -> Arrow (ListInt, ListInt)
    | CPlus -> Arrow (Int, Arrow (Int, Int))

let all_consts = [
    CUnit;
    CInt 0; CInt 1; CInt 2;
    CNil; CCons; CHd; CTl; CPlus;
]

let is_list_const = function
    | CNil | CCons | CHd | CTl -> true
    | CInt _ | CUnit | CPlus -> false

let rec term_depth = function
    | Var _ | Const _ -> 1
    | Lam (_, body) | TyLam body | MkRef body | Deref body -> 1 + term_depth body
    | TyApp (e, _) -> 1 + term_depth e
    | App (e1, e2) | Assign (e1, e2) | Seq (e1, e2) | Minus (e1, e2) ->
        1 + max (term_depth e1) (term_depth e2)
    | Ifz (e1, e2, e3) ->
        1 + max (term_depth e1) (max (term_depth e2) (term_depth e3))

let rec term_nodes = function
    | Var _ | Const _ -> 1
    | Lam (_, body) | TyLam body | MkRef body | Deref body -> 1 + term_nodes body
    | TyApp (e, _) -> 1 + term_nodes e
    | App (e1, e2) | Assign (e1, e2) | Seq (e1, e2) | Minus (e1, e2) ->
        1 + term_nodes e1 + term_nodes e2
    | Ifz (e1, e2, e3) -> 1 + term_nodes e1 + term_nodes e2 + term_nodes e3

let term_root = function
    | Var _ -> "var" | Lam _ -> "lam" | App _ -> "app" | Const _ -> "const"
    | TyLam _ -> "tylam" | TyApp _ -> "tyapp"
    | MkRef _ -> "mkref" | Deref _ -> "deref" | Assign _ -> "assign"
    | Seq _ -> "seq" | Minus _ -> "minus" | Ifz _ -> "ifz"

let rec term_binders = function
    | Var _ | Const _ -> 0
    | Lam (_, body) -> 1 + term_binders body
    | TyLam body | MkRef body | Deref body -> term_binders body
    | TyApp (e, _) -> term_binders e
    | App (e1, e2) | Assign (e1, e2) | Seq (e1, e2) | Minus (e1, e2) ->
        term_binders e1 + term_binders e2
    | Ifz (e1, e2, e3) -> term_binders e1 + term_binders e2 + term_binders e3

let fact_depth f = term_depth f.term
let fact_nodes f = term_nodes f.term
let fact_root f = term_root f.term
let fact_unique_vars f = term_binders f.term
