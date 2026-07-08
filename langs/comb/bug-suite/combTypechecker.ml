module C = CombPrograms

let rec typ_equal t1 t2 =
    match t1, t2 with
    | C.Int, C.Int -> true
    | C.Unit, C.Unit -> true
    | C.ListInt, C.ListInt -> true
    | C.Arrow (a1, b1), C.Arrow (a2, b2) -> typ_equal a1 a2 && typ_equal b1 b2
    | C.Ref a, C.Ref b -> typ_equal a b
    | C.Forall a, C.Forall b -> typ_equal a b
    | C.TyVar i, C.TyVar j -> i = j
    | C.TVar i, C.TVar j -> i = j
    | _ -> false

let rec well_formed d t =
    match t with
    | C.Int | C.Unit | C.ListInt -> true
    | C.Arrow (a, b) -> well_formed d a && well_formed d b
    | C.Ref a -> well_formed d a
    | C.Forall body -> well_formed (d + 1) body
    | C.TyVar i -> i >= 0 && i < d
    | C.TVar _ -> true

let const_type = function
    | C.CInt _ -> C.Int
    | C.CUnit -> C.Unit
    | C.CNil -> C.ListInt
    | C.CCons -> C.Arrow (C.Int, C.Arrow (C.ListInt, C.ListInt))
    | C.CHd -> C.Arrow (C.ListInt, C.Int)
    | C.CTl -> C.Arrow (C.ListInt, C.ListInt)
    | C.CPlus -> C.Arrow (C.Int, C.Arrow (C.Int, C.Int))

let rec typeof d ctx (e : C.term) : C.typ option =
    match e with
    | C.Var i ->
        if i >= 0 && i < List.length ctx then Some (List.nth ctx i) else None
    | C.Lam (t, body) ->
        if not (well_formed d t) then None
        else (match typeof d (t :: ctx) body with
         | Some t2 -> Some (C.Arrow (t, t2))
         | None -> None)
    | C.App (m, n) ->
        (match typeof d ctx m with
         | Some (C.Arrow (t1, t2)) ->
             (match typeof d ctx n with
              | Some t1' when typ_equal t1 t1' -> Some t2
              | _ -> None)
         | _ -> None)
    | C.Const c -> Some (const_type c)
    | C.TyLam body ->
        let shifted_ctx = List.map (C.shift_tyvar 0 1) ctx in
        (match typeof (d + 1) shifted_ctx body with
         | Some t -> Some (C.Forall t)
         | None -> None)
    | C.TyApp (e, t) ->
        if not (well_formed d t) then None
        else (match typeof d ctx e with
         | Some (C.Forall body) -> Some (C.subst_tyvar t body)
         | _ -> None)
    | C.MkRef e ->
        (match typeof d ctx e with
         | Some t -> Some (C.Ref t)
         | None -> None)
    | C.Deref e ->
        (match typeof d ctx e with
         | Some (C.Ref t) -> Some t
         | _ -> None)
    | C.Assign (e1, e2) ->
        (match typeof d ctx e1 with
         | Some (C.Ref t) ->
             (match typeof d ctx e2 with
              | Some t' when typ_equal t t' -> Some C.Unit
              | _ -> None)
         | _ -> None)
    | C.Seq (e1, e2) ->
        (match typeof d ctx e1 with
         | Some C.Unit -> typeof d ctx e2
         | _ -> None)
    | C.Minus (e1, e2) ->
        (match typeof d ctx e1, typeof d ctx e2 with
         | Some C.Int, Some C.Int -> Some C.Int
         | _ -> None)
    | C.Ifz (e1, e2, e3) ->
        (match typeof d ctx e1 with
         | Some C.Int ->
             (match typeof d ctx e2, typeof d ctx e3 with
              | Some t2, Some t3 when typ_equal t2 t3 -> Some t2
              | _ -> None)
         | _ -> None)

let typecheck (f : C.fact) : C.typ option =
    typeof 0 [] f.C.term

let agrees_with_fact (f : C.fact) : bool =
    match typeof 0 [] f.C.term with
    | None -> false
    | Some t -> typ_equal t f.C.typ
