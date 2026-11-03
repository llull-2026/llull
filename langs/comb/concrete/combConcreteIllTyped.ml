open CombPrograms
open CombConcretePrototerms

let rec lam_ann_sites path = function
    | Lam (ty, body) -> (path, ty) :: lam_ann_sites (path @ [0]) body
    | App (m, n) -> lam_ann_sites (path @ [0]) m @ lam_ann_sites (path @ [1]) n
    | TyLam body -> lam_ann_sites (path @ [0]) body
    | TyApp (e, _) -> lam_ann_sites (path @ [0]) e
    | MkRef e | Deref e -> lam_ann_sites (path @ [0]) e
    | Assign (e1, e2) | Seq (e1, e2) | Minus (e1, e2) ->
        lam_ann_sites (path @ [0]) e1 @ lam_ann_sites (path @ [1]) e2
    | Ifz (e1, e2, e3) ->
        lam_ann_sites (path @ [0]) e1
        @ lam_ann_sites (path @ [1]) e2
        @ lam_ann_sites (path @ [2]) e3
    | Var _ | Const _ -> []

let rec set_lam_ann path new_ty t =
    match t, path with
    | Lam (_, body), [] -> Lam (new_ty, body)
    | Lam (ty, body), 0 :: p -> Lam (ty, set_lam_ann p new_ty body)
    | App (m, n), 0 :: p -> App (set_lam_ann p new_ty m, n)
    | App (m, n), 1 :: p -> App (m, set_lam_ann p new_ty n)
    | TyLam body, 0 :: p -> TyLam (set_lam_ann p new_ty body)
    | TyApp (e, ty), 0 :: p -> TyApp (set_lam_ann p new_ty e, ty)
    | MkRef e, 0 :: p -> MkRef (set_lam_ann p new_ty e)
    | Deref e, 0 :: p -> Deref (set_lam_ann p new_ty e)
    | Assign (e1, e2), 0 :: p -> Assign (set_lam_ann p new_ty e1, e2)
    | Assign (e1, e2), 1 :: p -> Assign (e1, set_lam_ann p new_ty e2)
    | Seq (e1, e2), 0 :: p -> Seq (set_lam_ann p new_ty e1, e2)
    | Seq (e1, e2), 1 :: p -> Seq (e1, set_lam_ann p new_ty e2)
    | Minus (e1, e2), 0 :: p -> Minus (set_lam_ann p new_ty e1, e2)
    | Minus (e1, e2), 1 :: p -> Minus (e1, set_lam_ann p new_ty e2)
    | Ifz (e1, e2, e3), 0 :: p -> Ifz (set_lam_ann p new_ty e1, e2, e3)
    | Ifz (e1, e2, e3), 1 :: p -> Ifz (e1, set_lam_ann p new_ty e2, e3)
    | Ifz (e1, e2, e3), 2 :: p -> Ifz (e1, e2, set_lam_ann p new_ty e3)
    | t, _ -> t

let ann_alternatives ~no_lists =
    if no_lists then [Int; Unit; Arrow (Int, Int); Ref Int]
    else [Int; Unit; ListInt; Arrow (Int, Int); Ref Int]

let lam_ann_swap_variants ~no_lists s =
    if s.sctx <> [] || s.stylvl <> 0 then []
    else
    lam_ann_sites [] s.sterm
    |> List.concat_map (fun (ann_path, current) ->
        List.filter_map (fun alt ->
            if alt = current then None
            else Some { s with sterm = set_lam_ann ann_path alt s.sterm })
            (ann_alternatives ~no_lists))

let techniques =
    [ (fun (config : CombConcretePrototerms.config) s -> List.to_seq
          (lam_ann_swap_variants
              ~no_lists:config.CombConcretePrototerms.no_lists s)) ]
