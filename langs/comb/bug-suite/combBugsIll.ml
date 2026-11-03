module C = CombPrograms
module Co = CombTypechecker

type go_fn = int -> C.typ list -> C.term -> C.typ option

type rules = {
    var    : go_fn -> int -> C.typ list -> int -> C.typ option;
    lam    : go_fn -> int -> C.typ list -> C.typ -> C.term -> C.typ option;
    app    : go_fn -> int -> C.typ list -> C.term -> C.term -> C.typ option;
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
        | C.Const c -> Some (Co.const_type c)
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
    | Some t2 -> Some (C.Arrow (t, t2))
    | None -> None)

let default_app go d ctx m n =
    match go d ctx m with
    | Some (C.Arrow (t1, t2)) ->
        (match go d ctx n with
         | Some t1' when Co.typ_equal t1 t1' -> Some t2
         | _ -> None)
    | _ -> None

let default_tylam go d ctx body =
    let shifted = List.map (C.shift_tyvar 0 1) ctx in
    (match go (d + 1) shifted body with
     | Some t -> Some (C.Forall t)
     | None -> None)

let default_tyapp go d ctx e t =
    if not (Co.well_formed d t) then None
    else (match go d ctx e with
    | Some (C.Forall body) -> Some (C.subst_tyvar t body)
    | _ -> None)

let default_mkref go d ctx e =
    match go d ctx e with Some t -> Some (C.Ref t) | None -> None

let default_deref go d ctx e =
    match go d ctx e with Some (C.Ref t) -> Some t | _ -> None

let default_assign go d ctx e1 e2 =
    match go d ctx e1 with
    | Some (C.Ref t) ->
        (match go d ctx e2 with
         | Some t' when Co.typ_equal t t' -> Some C.Unit
         | _ -> None)
    | _ -> None

let default_seq go d ctx e1 e2 =
    match go d ctx e1 with
    | Some C.Unit -> go d ctx e2
    | _ -> None

let default_minus go d ctx e1 e2 =
    match go d ctx e1, go d ctx e2 with
    | Some C.Int, Some C.Int -> Some C.Int
    | _ -> None

let default_ifz go d ctx e1 e2 e3 =
    match go d ctx e1 with
    | Some C.Int ->
        (match go d ctx e2, go d ctx e3 with
         | Some t2, Some t3 when Co.typ_equal t2 t3 -> Some t2
         | _ -> None)
    | _ -> None

let default_rules = {
    var = default_var; lam = default_lam; app = default_app;
    tylam = default_tylam; tyapp = default_tyapp;
    mkref = default_mkref; deref = default_deref; assign = default_assign;
    seq = default_seq; minus = default_minus; ifz = default_ifz;
}

let alt_type = function
    | C.Int -> C.Unit
    | C.Unit -> C.Int
    | C.ListInt -> C.Int
    | C.Arrow _ -> C.Int
    | C.Ref _ -> C.Int
    | C.Forall _ -> C.Int
    | C.TyVar _ -> C.Int
    | C.TVar _ -> C.Int

let bug_app_arg = { default_rules with
    app = fun go d ctx m n ->
        match go d ctx m with
        | Some (C.Arrow (_t1, t2)) ->
            (match go d ctx n with
             | Some _ -> Some t2
             | None -> None)
        | _ -> None
}

let bug_app_head = { default_rules with
    app = fun go d ctx m n ->
        match go d ctx m with
        | Some (C.Arrow (t1, t2)) ->
            (match go d ctx n with
             | Some t1' when Co.typ_equal t1 t1' -> Some t2
             | _ -> None)
        | Some _ ->
            (match go d ctx n with
             | Some _ -> Some C.Int
             | None -> None)
        | None -> None
}

let bug_lam_binder = { default_rules with
    lam = fun go d ctx t body ->
        let bogus = alt_type t in
        match go d (bogus :: ctx) body with
        | Some t2 -> Some (C.Arrow (t, t2))
        | None -> None
}

let bug_var_bounds = { default_rules with
    var = fun _go _d ctx i ->
        if i >= 0 && i < List.length ctx then Some (List.nth ctx i)
        else Some C.Int
}

let bug_lam_body = { default_rules with
    lam = fun _go _d _ctx t _body ->
        Some (C.Arrow (t, C.Int))
}

let bug_tylam_body = { default_rules with
    tylam = fun _go _d _ctx _body ->
        Some (C.Forall C.Int)
}

let bug_tyapp_head = { default_rules with
    tyapp = fun go d ctx e t ->
        match go d ctx e with
        | Some (C.Forall body) -> Some (C.subst_tyvar t body)
        | Some _ -> Some C.Int
        | None -> None
}

let bug_deref_ref = { default_rules with
    deref = fun go d ctx e ->
        match go d ctx e with
        | Some (C.Ref t) -> Some t
        | Some t -> Some t
        | None -> None
}

let bug_assign_rhs = { default_rules with
    assign = fun go d ctx e1 e2 ->
        match go d ctx e1 with
        | Some (C.Ref _) ->
            (match go d ctx e2 with
             | Some _ -> Some C.Unit
             | None -> None)
        | _ -> None
}

let bug_assign_lhs = { default_rules with
    assign = fun go d ctx e1 e2 ->
        match go d ctx e1 with
        | Some _ ->
            (match go d ctx e2 with
             | Some _ -> Some C.Unit
             | None -> None)
        | None -> None
}

let bug_seq_unit = { default_rules with
    seq = fun go d ctx e1 e2 ->
        match go d ctx e1 with
        | Some _ -> go d ctx e2
        | None -> None
}

let bug_minus_lhs = { default_rules with
    minus = fun go d ctx e1 e2 ->
        match go d ctx e1, go d ctx e2 with
        | Some _, Some C.Int -> Some C.Int
        | _ -> None
}

let bug_minus_rhs = { default_rules with
    minus = fun go d ctx e1 e2 ->
        match go d ctx e1, go d ctx e2 with
        | Some C.Int, Some _ -> Some C.Int
        | _ -> None
}

let bug_ifz_guard = { default_rules with
    ifz = fun go d ctx e1 e2 e3 ->
        match go d ctx e1 with
        | Some _ ->
            (match go d ctx e2, go d ctx e3 with
             | Some t2, Some t3 when Co.typ_equal t2 t3 -> Some t2
             | _ -> None)
        | None -> None
}

let bug_ifz_branches = { default_rules with
    ifz = fun go d ctx e1 e2 e3 ->
        match go d ctx e1 with
        | Some C.Int ->
            (match go d ctx e2, go d ctx e3 with
             | Some t2, Some _ -> Some t2
             | _ -> None)
        | _ -> None
}

let bug_lam_wf = { default_rules with
    lam = fun go d ctx t body ->
        match go d (t :: ctx) body with
        | Some t2 -> Some (C.Arrow (t, t2))
        | None -> None
}

let bug_tyapp_wf = { default_rules with
    tyapp = fun go d ctx e t ->
        match go d ctx e with
        | Some (C.Forall body) -> Some (C.subst_tyvar t body)
        | _ -> None
}

let bug_cc_assign_poly = { default_rules with
    assign = fun go d ctx e1 e2 ->
        match go d ctx e1 with
        | Some (C.Ref (C.Forall _)) ->
            (match go d ctx e2 with
             | Some _ -> Some C.Unit
             | None -> None)
        | Some (C.Ref t) ->
            (match go d ctx e2 with
             | Some t' when Co.typ_equal t t' -> Some C.Unit
             | _ -> None)
        | _ -> None
}

let bug_cc_seq_poly = { default_rules with
    seq = fun go d ctx e1 e2 ->
        match go d ctx e1 with
        | Some C.Unit -> go d ctx e2
        | Some (C.Forall _) -> go d ctx e2
        | _ -> None
}

let bug_cc_tyapp_ref = { default_rules with
    tyapp = fun go d ctx e t ->
        if not (Co.well_formed d t) then None
        else (match go d ctx e with
        | Some (C.Forall body) -> Some (C.subst_tyvar t body)
        | Some (C.Ref (C.Forall body)) -> Some (C.subst_tyvar t body)
        | _ -> None)
}

let bug_exposed rules (fact : C.fact) =
    match Co.typecheck fact with
    | Some _ -> false
    | None ->
        (match make_typeof rules 0 [] fact.C.term with
         | Some _ -> true
         | None -> false)

let make name bug_id severity description rules =
    (name, "combined-neg", bug_id, severity, description, `Reject,
     (fun fact -> bug_exposed rules fact))

let inherited_bugs = [
    make "combined-neg-app-arg" 1 `Shallow
        "App: doesn't check argument type matches function domain" bug_app_arg;
    make "combined-neg-app-head" 2 `Shallow
        "App: doesn't check head is a function type" bug_app_head;
    make "combined-neg-lam-binder" 3 `Medium
        "Lam: ignores binder annotation when checking body" bug_lam_binder;
    make "combined-neg-var" 4 `Shallow
        "Var: accepts out-of-range de Bruijn indices" bug_var_bounds;
    make "combined-neg-lam-body" 5 `Medium
        "Lam: doesn't check the body typechecks under the extended context" bug_lam_body;
    make "combined-neg-tylam-body" 6 `Medium
        "TyLam: doesn't check the body typechecks under the extended type context" bug_tylam_body;
    make "combined-neg-tyapp-head" 7 `Shallow
        "TyApp: doesn't check the head has Forall type" bug_tyapp_head;
    make "combined-neg-deref" 8 `Shallow
        "Deref: doesn't check operand has Ref type" bug_deref_ref;
    make "combined-neg-assign-rhs" 9 `Shallow
        "Assign: doesn't check rhs type matches cell content type" bug_assign_rhs;
    make "combined-neg-assign-lhs" 10 `Shallow
        "Assign: doesn't check lhs has Ref type" bug_assign_lhs;
    make "combined-neg-seq" 11 `Shallow
        "Seq: doesn't require LHS of `;` to have Unit type" bug_seq_unit;
    make "combined-neg-minus-lhs" 12 `Shallow
        "Minus: doesn't check LHS has Int type" bug_minus_lhs;
    make "combined-neg-minus-rhs" 13 `Shallow
        "Minus: doesn't check RHS has Int type" bug_minus_rhs;
    make "combined-neg-ifz-guard" 14 `Shallow
        "Ifz: doesn't check guard has Int type" bug_ifz_guard;
    make "combined-neg-ifz-branches" 15 `Shallow
        "Ifz: doesn't check then/else branches have the same type" bug_ifz_branches;
    make "combined-neg-lam-wf" 16 `Medium
        "Lam: doesn't check the binder annotation is well-formed (no free type variables)" bug_lam_wf;
    make "combined-neg-tyapp-wf" 17 `Medium
        "TyApp: doesn't check the type argument is well-formed (no free type variables)" bug_tyapp_wf;
]

let cross_cutting_bugs = [
    make "combined-cc-assign-poly" 18 `Medium
        "Assign (Ref×SysF): skips the rhs/cell type-match check when the cell content type is polymorphic (Forall)" bug_cc_assign_poly;
    make "combined-cc-seq-poly" 19 `Medium
        "Seq (Ref×SysF): accepts a polymorphic (Forall) LHS as if it had Unit type" bug_cc_seq_poly;
    make "combined-cc-tyapp-ref" 20 `Medium
        "TyApp (Ref×SysF): accepts a Ref-wrapped Forall head, peeking through the Ref" bug_cc_tyapp_ref;
]

let bugs =
    inherited_bugs @ cross_cutting_bugs
