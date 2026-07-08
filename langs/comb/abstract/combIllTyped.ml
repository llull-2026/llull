open CombPrograms
open CombPrototerms
open CombConcretization

let rec count_tvar v = function
    | Int | Unit | ListInt | TyVar _ -> 0
    | TVar w -> if v = w then 1 else 0
    | Arrow (a, b) -> count_tvar v a + count_tvar v b
    | Forall body -> count_tvar v body
    | Ref t -> count_tvar v t

let rec leaf_tvar_paths = function
    | Int | Unit | ListInt | TyVar _ -> []
    | TVar v -> [(v, fun r -> r)]
    | Arrow (a, b) ->
        List.map (fun (v, reb) -> (v, fun r -> Arrow (reb r, b))) (leaf_tvar_paths a)
        @ List.map (fun (v, reb) -> (v, fun r -> Arrow (a, reb r))) (leaf_tvar_paths b)
    | Forall body ->
        List.map (fun (v, reb) -> (v, fun r -> Forall (reb r))) (leaf_tvar_paths body)
    | Ref t ->
        List.map (fun (v, reb) -> (v, fun r -> Ref (reb r))) (leaf_tvar_paths t)

let rec lam_sites path = function
    | SLam (ty, body) -> (path, ty) :: lam_sites (path @ [0]) body
    | SApp (m, n) -> lam_sites (path @ [0]) m @ lam_sites (path @ [1]) n
    | STyLam body -> lam_sites (path @ [0]) body
    | STyApp (body, _) -> lam_sites (path @ [0]) body
    | SMkRef e -> lam_sites (path @ [0]) e
    | SDeref e -> lam_sites (path @ [0]) e
    | SAssign (e1, e2) -> lam_sites (path @ [0]) e1 @ lam_sites (path @ [1]) e2
    | SSeq (e1, e2) -> lam_sites (path @ [0]) e1 @ lam_sites (path @ [1]) e2
    | SMinus (e1, e2) -> lam_sites (path @ [0]) e1 @ lam_sites (path @ [1]) e2
    | SIfz (e1, e2, e3) ->
        lam_sites (path @ [0]) e1 @ lam_sites (path @ [1]) e2 @ lam_sites (path @ [2]) e3
    | SBound _ | SFree _ | SConst _ -> []

let rec rewrite_at_path path f t =
    match path with
    | [] -> f t
    | i :: p ->
        let go = rewrite_at_path p f in
        (match t, i with
         | SLam (ty, body), 0 -> SLam (ty, go body)
         | SApp (m, n), 0 -> SApp (go m, n)
         | SApp (m, n), 1 -> SApp (m, go n)
         | STyLam body, 0 -> STyLam (go body)
         | STyApp (body, ty), 0 -> STyApp (go body, ty)
         | SMkRef e, 0 -> SMkRef (go e)
         | SDeref e, 0 -> SDeref (go e)
         | SAssign (e1, e2), 0 -> SAssign (go e1, e2)
         | SAssign (e1, e2), 1 -> SAssign (e1, go e2)
         | SSeq (e1, e2), 0 -> SSeq (go e1, e2)
         | SSeq (e1, e2), 1 -> SSeq (e1, go e2)
         | SMinus (e1, e2), 0 -> SMinus (go e1, e2)
         | SMinus (e1, e2), 1 -> SMinus (e1, go e2)
         | SIfz (e1, e2, e3), 0 -> SIfz (go e1, e2, e3)
         | SIfz (e1, e2, e3), 1 -> SIfz (e1, go e2, e3)
         | SIfz (e1, e2, e3), 2 -> SIfz (e1, e2, go e3)
         | _ -> t)

let set_ann path new_ty t =
    rewrite_at_path path
        (function SLam (_, body) -> SLam (new_ty, body) | t -> t) t

let disidentify_variants s =
    let sites = lam_sites [] s.sterm in
    let total v = List.fold_left (fun acc (_, ty) -> acc + count_tvar v ty) 0 sites in
    let next_tvar = ref s.next_tvar in
    let variants = ref [] in
    List.iter (fun (ann_path, ann) ->
        leaf_tvar_paths ann |> List.iter (fun (v, rebuild) ->
            if total v >= 2 then begin
                let f = !next_tvar in incr next_tvar;
                let new_ann = rebuild (TVar f) in
                let new_sterm = set_ann ann_path new_ann s.sterm in
                variants := { s with
                    sterm = new_sterm;
                    type_neqs = (TVar v, TVar f) :: s.type_neqs;
                    next_tvar = !next_tvar;
                } :: !variants
            end)
    ) sites;
    List.rev !variants

let constructor_swap_variants ~no_lists s =
    let sites = lam_sites [] s.sterm in
    let next_tvar = ref s.next_tvar in
    let variants = ref [] in
    let fresh () = let f = !next_tvar in incr next_tvar; TVar f in
    let emit ann_path new_ann =
        if no_lists && new_ann = ListInt then ()
        else variants := { s with
            sterm = set_ann ann_path new_ann s.sterm;
            next_tvar = !next_tvar;
        } :: !variants in
    let candidates = [
        `Int,   (fun () -> Int);
        `Unit,  (fun () -> Unit);
        `List,  (fun () -> ListInt);
        `Arrow, (fun () -> Arrow (fresh (), fresh ()));
        `Ref,   (fun () -> Ref (fresh ())) ] in
    let head_of = function
        | Int -> Some `Int | Unit -> Some `Unit | ListInt -> Some `List
        | Arrow _ -> Some `Arrow | Ref _ -> Some `Ref
        | Forall _ -> Some `Forall
        | TVar _ | TyVar _ -> None in
    List.iter (fun (ann_path, ann) ->
        match head_of ann with
        | None -> ()
        | Some h ->
            List.iter (fun (h', mk) ->
                if h' <> h then emit ann_path (mk ())) candidates
    ) sites;
    List.rev !variants

let rec sbound_sites depth path = function
    | SBound _ -> [(path, depth)]
    | SFree _ | SConst _ -> []
    | SLam (_, body) -> sbound_sites (depth + 1) (path @ [0]) body
    | SApp (m, n) ->
        sbound_sites depth (path @ [0]) m
        @ sbound_sites depth (path @ [1]) n
    | STyLam body -> sbound_sites depth (path @ [0]) body
    | STyApp (body, _) -> sbound_sites depth (path @ [0]) body
    | SMkRef e -> sbound_sites depth (path @ [0]) e
    | SDeref e -> sbound_sites depth (path @ [0]) e
    | SAssign (e1, e2) ->
        sbound_sites depth (path @ [0]) e1
        @ sbound_sites depth (path @ [1]) e2
    | SSeq (e1, e2) ->
        sbound_sites depth (path @ [0]) e1
        @ sbound_sites depth (path @ [1]) e2
    | SMinus (e1, e2) ->
        sbound_sites depth (path @ [0]) e1
        @ sbound_sites depth (path @ [1]) e2
    | SIfz (e1, e2, e3) ->
        sbound_sites depth (path @ [0]) e1
        @ sbound_sites depth (path @ [1]) e2
        @ sbound_sites depth (path @ [2]) e3

let set_sbound_idx path new_idx t =
    rewrite_at_path path
        (function SBound (_, info) -> SBound (new_idx, info) | t -> t) t

let out_of_scope_variants s =
    sbound_sites 0 [] s.sterm
    |> List.map (fun (path, depth) ->
        { s with sterm = set_sbound_idx path depth s.sterm })

let tyvar_occurrence_variants base ty =
    let results = ref [] in
    let rec go local_depth rebuild t =
        match t with
        | TyVar _ ->
            let free_idx = base + local_depth in
            results := rebuild (TyVar free_idx) :: !results
        | Arrow (a, b) ->
            go local_depth (fun a' -> rebuild (Arrow (a', b))) a;
            go local_depth (fun b' -> rebuild (Arrow (a, b'))) b
        | Ref a -> go local_depth (fun a' -> rebuild (Ref a')) a
        | Forall body -> go (local_depth + 1) (fun b' -> rebuild (Forall b')) body
        | Int | Unit | ListInt | TVar _ -> ()
    in
    go 0 (fun x -> x) ty;
    List.rev !results

let rec tyvar_oos_sterm_variants tydepth t =
    match t with
    | SBound _ | SFree _ | SConst _ -> []
    | SLam (ty, body) ->
        List.map (fun ty' -> SLam (ty', body)) (tyvar_occurrence_variants tydepth ty)
        @ List.map (fun b' -> SLam (ty, b')) (tyvar_oos_sterm_variants tydepth body)
    | STyApp (e, ty) ->
        List.map (fun ty' -> STyApp (e, ty')) (tyvar_occurrence_variants tydepth ty)
        @ List.map (fun e' -> STyApp (e', ty)) (tyvar_oos_sterm_variants tydepth e)
    | STyLam body ->
        List.map (fun b' -> STyLam b') (tyvar_oos_sterm_variants (tydepth + 1) body)
    | SApp (m, n) ->
        List.map (fun m' -> SApp (m', n)) (tyvar_oos_sterm_variants tydepth m)
        @ List.map (fun n' -> SApp (m, n')) (tyvar_oos_sterm_variants tydepth n)
    | SMkRef e -> List.map (fun e' -> SMkRef e') (tyvar_oos_sterm_variants tydepth e)
    | SDeref e -> List.map (fun e' -> SDeref e') (tyvar_oos_sterm_variants tydepth e)
    | SAssign (e1, e2) ->
        List.map (fun x -> SAssign (x, e2)) (tyvar_oos_sterm_variants tydepth e1)
        @ List.map (fun x -> SAssign (e1, x)) (tyvar_oos_sterm_variants tydepth e2)
    | SSeq (e1, e2) ->
        List.map (fun x -> SSeq (x, e2)) (tyvar_oos_sterm_variants tydepth e1)
        @ List.map (fun x -> SSeq (e1, x)) (tyvar_oos_sterm_variants tydepth e2)
    | SMinus (e1, e2) ->
        List.map (fun x -> SMinus (x, e2)) (tyvar_oos_sterm_variants tydepth e1)
        @ List.map (fun x -> SMinus (e1, x)) (tyvar_oos_sterm_variants tydepth e2)
    | SIfz (e1, e2, e3) ->
        List.map (fun x -> SIfz (x, e2, e3)) (tyvar_oos_sterm_variants tydepth e1)
        @ List.map (fun x -> SIfz (e1, x, e3)) (tyvar_oos_sterm_variants tydepth e2)
        @ List.map (fun x -> SIfz (e1, e2, x)) (tyvar_oos_sterm_variants tydepth e3)

let tyvar_out_of_scope_variants s =
    tyvar_oos_sterm_variants 0 s.sterm
    |> List.map (fun st -> { s with sterm = st })

let techniques =
    let t variants = fun config s ->
        List.to_seq (variants (auto_close_if_needed config s)) in
    [
        t disidentify_variants;
        (fun config s ->
            List.to_seq (constructor_swap_variants
                ~no_lists:config.no_lists
                (auto_close_if_needed config s)));
        t out_of_scope_variants;
        t tyvar_out_of_scope_variants;
    ]
