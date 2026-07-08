module C = CombPrograms
module Co = CombTypechecker

type go_fn = int -> C.typ list -> C.term -> C.typ option

type rules = {
    var    : go_fn -> int -> C.typ list -> int -> C.typ option;
    lam    : go_fn -> int -> C.typ list -> C.typ -> C.term -> C.typ option;
    app    : go_fn -> int -> C.typ list -> C.term -> C.term -> C.typ option;
    const  : C.const -> C.typ option;
    tylam  : go_fn -> int -> C.typ list -> C.term -> C.typ option;
    tyapp  : go_fn -> int -> C.typ list -> C.term -> C.typ -> C.typ option;
    mkref  : go_fn -> int -> C.typ list -> C.term -> C.typ option;
    deref  : go_fn -> int -> C.typ list -> C.term -> C.typ option;
    assign : go_fn -> int -> C.typ list -> C.term -> C.term -> C.typ option;
    seq    : go_fn -> int -> C.typ list -> C.term -> C.term -> C.typ option;
    minus  : go_fn -> int -> C.typ list -> C.term -> C.term -> C.typ option;
    ifz    : go_fn -> int -> C.typ list -> C.term -> C.term -> C.term -> C.typ option;
}

let make_typeof (r : rules) : go_fn =
    let rec go d ctx e =
        match e with
        | C.Var i -> r.var go d ctx i
        | C.Lam (t, b) -> r.lam go d ctx t b
        | C.App (m, n) -> r.app go d ctx m n
        | C.Const c -> r.const c
        | C.TyLam b -> r.tylam go d ctx b
        | C.TyApp (e, t) -> r.tyapp go d ctx e t
        | C.MkRef e -> r.mkref go d ctx e
        | C.Deref e -> r.deref go d ctx e
        | C.Assign (e1, e2) -> r.assign go d ctx e1 e2
        | C.Seq (e1, e2) -> r.seq go d ctx e1 e2
        | C.Minus (e1, e2) -> r.minus go d ctx e1 e2
        | C.Ifz (e1, e2, e3) -> r.ifz go d ctx e1 e2 e3
    in
    go

let default_var _go _d ctx i =
    if i >= 0 && i < List.length ctx then Some (List.nth ctx i) else None

let default_lam go d ctx t body =
    if not (Co.well_formed d t) then None
    else (match go d (t :: ctx) body with
          | Some t2 -> Some (C.Arrow (t, t2)) | None -> None)

let default_app go d ctx m n =
    match go d ctx m with
    | Some (C.Arrow (t1, t2)) ->
        (match go d ctx n with Some t1' when Co.typ_equal t1 t1' -> Some t2 | _ -> None)
    | _ -> None

let default_const c = Some (Co.const_type c)

let default_tylam go d ctx body =
    let shifted = List.map (C.shift_tyvar 0 1) ctx in
    (match go (d + 1) shifted body with Some t -> Some (C.Forall t) | None -> None)

let default_tyapp go d ctx e t =
    if not (Co.well_formed d t) then None
    else (match go d ctx e with
          | Some (C.Forall body) -> Some (C.subst_tyvar t body) | _ -> None)

let default_mkref go d ctx e = match go d ctx e with Some t -> Some (C.Ref t) | None -> None
let default_deref go d ctx e = match go d ctx e with Some (C.Ref t) -> Some t | _ -> None

let default_assign go d ctx e1 e2 =
    match go d ctx e1 with
    | Some (C.Ref t) ->
        (match go d ctx e2 with Some t' when Co.typ_equal t t' -> Some C.Unit | _ -> None)
    | _ -> None

let default_seq go d ctx e1 e2 =
    match go d ctx e1 with Some C.Unit -> go d ctx e2 | _ -> None

let default_minus go d ctx e1 e2 =
    match go d ctx e1, go d ctx e2 with Some C.Int, Some C.Int -> Some C.Int | _ -> None

let default_ifz go d ctx e1 e2 e3 =
    match go d ctx e1 with
    | Some C.Int ->
        (match go d ctx e2, go d ctx e3 with
         | Some t2, Some t3 when Co.typ_equal t2 t3 -> Some t2 | _ -> None)
    | _ -> None

let default_rules = {
    var = default_var; lam = default_lam; app = default_app; const = default_const;
    tylam = default_tylam; tyapp = default_tyapp;
    mkref = default_mkref; deref = default_deref; assign = default_assign;
    seq = default_seq; minus = default_minus; ifz = default_ifz;
}

let bug_app_codomain = { default_rules with
    app = fun go d ctx m n ->
        match go d ctx m with
        | Some (C.Arrow (_t1, t2)) ->
            (match go d ctx n with
             | Some t2' when Co.typ_equal t2 t2' -> Some t2
             | _ -> None)
        | _ -> None
}

let bug_app_swap = { default_rules with
    app = fun go d ctx m n ->
        match go d ctx m with
        | Some (C.Arrow (t1, t2)) ->
            (match go d ctx n with
             | Some t2' when Co.typ_equal t2 t2' -> Some t1
             | _ -> None)
        | _ -> None
}

let const_cons = function
    | C.CCons -> Some (C.Arrow (C.Int, C.Int))
    | c -> Some (Co.const_type c)
let bug_cons_arity = { default_rules with const = const_cons }

let const_plus = function
    | C.CPlus -> Some (C.Arrow (C.Int, C.Int))
    | c -> Some (Co.const_type c)
let bug_plus_arity = { default_rules with const = const_plus }

let const_hd = function
    | C.CHd -> Some (C.Arrow (C.ListInt, C.ListInt))
    | c -> Some (Co.const_type c)
let bug_hd_type = { default_rules with const = const_hd }

let const_tl = function
    | C.CTl -> Some (C.Arrow (C.ListInt, C.Int))
    | c -> Some (Co.const_type c)
let bug_tl_type = { default_rules with const = const_tl }

let bug_lookup_int = { default_rules with
    var = fun _go _d ctx i ->
        if i >= 0 && i < List.length ctx then Some C.Int else None
}

let bug_lookup_head = { default_rules with
    var = fun _go _d ctx _i ->
        (match ctx with t :: _ -> Some t | [] -> None)
}

let bug_lam_swap = { default_rules with
    lam = fun go d ctx t body ->
        if not (Co.well_formed d t) then None
        else (match go d (t :: ctx) body with
              | Some t2 -> Some (C.Arrow (t2, t))
              | None -> None)
}

let bug_tyapp_no_subst = { default_rules with
    tyapp = fun go d ctx e t ->
        if not (Co.well_formed d t) then None
        else (match go d ctx e with
              | Some (C.Forall body) -> Some body
              | _ -> None)
}

let bug_tyapp_keep_forall = { default_rules with
    tyapp = fun go d ctx e t ->
        if not (Co.well_formed d t) then None
        else (match go d ctx e with
              | Some (C.Forall body) -> Some (C.Forall body)
              | _ -> None)
}

let bug_tylam_no_extend = { default_rules with
    tylam = fun go d ctx body ->
        (match go d ctx body with
         | Some t -> Some (C.Forall t) | None -> None)
}

let bug_deref_ref = { default_rules with
    deref = fun go d ctx e ->
        match go d ctx e with
        | Some (C.Ref t) -> Some (C.Ref t)
        | _ -> None
}

let bug_assign_ret = { default_rules with
    assign = fun go d ctx e1 e2 ->
        match go d ctx e1 with
        | Some (C.Ref t) ->
            (match go d ctx e2 with
             | Some t' when Co.typ_equal t t' -> Some (C.Ref t)
             | _ -> None)
        | _ -> None
}

let bug_seq_ret = { default_rules with
    seq = fun go d ctx e1 e2 ->
        match go d ctx e1 with
        | Some C.Unit ->
            (match go d ctx e2 with
             | Some _ -> Some C.Unit
             | None -> None)
        | _ -> None
}

let bug_app_domain = { default_rules with
    app = fun go d ctx m n ->
        match go d ctx m with
        | Some (C.Arrow (t1, t2)) ->
            (match go d ctx n with
             | Some t1' when Co.typ_equal t1 t1' -> Some t1
             | _ -> None)
        | _ -> None
}

let bug_mkref_nowrap = { default_rules with
    mkref = fun go d ctx e ->
        match go d ctx e with Some t -> Some t | None -> None
}

let bug_ifz_int = { default_rules with
    ifz = fun go d ctx e1 e2 e3 ->
        match go d ctx e1 with
        | Some C.Int ->
            (match go d ctx e2, go d ctx e3 with
             | Some t2, Some t3 when Co.typ_equal t2 t3 -> let _ = t2 in Some C.Int
             | _ -> None)
        | _ -> None
}

let rejects_well_typed rules (fact : C.fact) =
    match Co.typecheck fact with
    | None -> true
    | Some _ ->
        (match make_typeof rules 0 [] fact.C.term with
         | None -> false
         | Some _ -> true)

let make name bug_id severity description rules =
    (name, "combined", bug_id, severity, description, `Accept,
     (fun fact -> rejects_well_typed rules fact))

let bugs = [
    make "combined-app-codomain" 1 `Shallow
        "App: argument matched against the codomain (range) instead of the domain" bug_app_codomain;
    make "combined-app-swap" 2 `Shallow
        "App: domain and codomain swapped in the function position" bug_app_swap;
    make "combined-cons-arity" 3 `Shallow
        "cons has type (int -> int) instead of (int -> (list int) -> (list int))" bug_cons_arity;
    make "combined-plus-arity" 4 `Shallow
        "plus has type (int -> int) instead of (int -> int -> int)" bug_plus_arity;
    make "combined-hd-type" 5 `Shallow
        "hd has type (list int) -> (list int) instead of (list int) -> int" bug_hd_type;
    make "combined-tl-type" 6 `Shallow
        "tl has type (list int) -> int instead of (list int) -> (list int)" bug_tl_type;
    make "combined-lookup-int" 7 `Unnatural
        "lookup always returns int regardless of the binding's type" bug_lookup_int;
    make "combined-lookup-head" 8 `Shallow
        "lookup ignores the de Bruijn index and returns the innermost binding" bug_lookup_head;
    make "combined-lam-swap" 9 `Shallow
        "Lam returns the Arrow with domain and codomain swapped" bug_lam_swap;
    make "combined-tyapp-no-subst" 10 `Shallow
        "TyApp returns the forall-body without substituting the type argument" bug_tyapp_no_subst;
    make "combined-tyapp-keep-forall" 11 `Shallow
        "TyApp returns the whole Forall type (leaves the binder in place)" bug_tyapp_keep_forall;
    make "combined-tylam-no-extend" 12 `Medium
        "TyLam does not extend the type scope (depth/context) when checking its body" bug_tylam_no_extend;
    make "combined-deref" 13 `Shallow
        "deref returns (Ref t) instead of t" bug_deref_ref;
    make "combined-assign-ret" 14 `Shallow
        "assign returns (Ref t) instead of Unit" bug_assign_ret;
    make "combined-seq-ret" 15 `Shallow
        "seq returns Unit instead of the type of its right operand" bug_seq_ret;
    make "combined-app-domain" 16 `Shallow
        "application returns the domain instead of the codomain" bug_app_domain;
    make "combined-mkref-nowrap" 17 `Shallow
        "ref e has type t instead of (Ref t)" bug_mkref_nowrap;
    make "combined-ifz-int" 18 `Medium
        "ifz always returns Int regardless of the branch types" bug_ifz_int;
]
