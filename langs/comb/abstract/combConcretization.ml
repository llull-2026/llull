open CombPrograms
open CombPrototerms

let rec tvars_in_typ t =
    match t with
    | Int | Unit | ListInt | TyVar _ -> IntSet.empty
    | TVar i -> IntSet.singleton i
    | Arrow (t1, t2) -> IntSet.union (tvars_in_typ t1) (tvars_in_typ t2)
    | Forall body -> tvars_in_typ body
    | Ref t -> tvars_in_typ t

let rec tvars_in_sterm t =
    match t with
    | SBound _ | SFree _ | SConst _ -> IntSet.empty
    | SLam (ty, body) -> IntSet.union (tvars_in_typ ty) (tvars_in_sterm body)
    | SApp (t1, t2) -> IntSet.union (tvars_in_sterm t1) (tvars_in_sterm t2)
    | STyLam body -> tvars_in_sterm body
    | STyApp (e, ty) -> IntSet.union (tvars_in_sterm e) (tvars_in_typ ty)
    | SMkRef e -> tvars_in_sterm e
    | SDeref e -> tvars_in_sterm e
    | SAssign (e1, e2) -> IntSet.union (tvars_in_sterm e1) (tvars_in_sterm e2)
    | SSeq (e1, e2) -> IntSet.union (tvars_in_sterm e1) (tvars_in_sterm e2)
    | SMinus (e1, e2) -> IntSet.union (tvars_in_sterm e1) (tvars_in_sterm e2)
    | SIfz (e1, e2, e3) ->
        IntSet.union (tvars_in_sterm e1) @@
        IntSet.union (tvars_in_sterm e2) (tvars_in_sterm e3)

let tvars_in_sym_map m =
    IntMap.fold (fun _ info acc -> IntSet.union acc (tvars_in_typ info.sym_type)) m IntSet.empty

let tvars_in_eqs eqs =
    List.fold_left (fun acc (t1, t2) ->
        IntSet.union acc @@ IntSet.union (tvars_in_typ t1) (tvars_in_typ t2)) IntSet.empty eqs

let tvars_in_prototerm s =
    IntSet.union (tvars_in_typ s.styp) @@
    IntSet.union (tvars_in_sterm s.sterm) @@
    IntSet.union (tvars_in_sym_map s.sym_map) @@
    IntSet.union (tvars_in_eqs s.type_eqs) (tvars_in_eqs s.type_neqs)

let rec rename_typ offset t =
    match t with
    | Int | Unit | ListInt | TyVar _ -> t
    | TVar i -> TVar (i + offset)
    | Arrow (t1, t2) -> Arrow (rename_typ offset t1, rename_typ offset t2)
    | Forall body -> Forall (rename_typ offset body)
    | Ref t -> Ref (rename_typ offset t)

let rec rename_sterm offset t =
    match t with
    | SBound (i, info) -> SBound (i, Option.map (fun (id, ty) -> (id, rename_typ offset ty)) info)
    | SFree id -> SFree id
    | SLam (ty, body) -> SLam (rename_typ offset ty, rename_sterm offset body)
    | SApp (t1, t2) -> SApp (rename_sterm offset t1, rename_sterm offset t2)
    | SConst c -> SConst c
    | STyLam body -> STyLam (rename_sterm offset body)
    | STyApp (e, ty) -> STyApp (rename_sterm offset e, rename_typ offset ty)
    | SMkRef e -> SMkRef (rename_sterm offset e)
    | SDeref e -> SDeref (rename_sterm offset e)
    | SAssign (e1, e2) -> SAssign (rename_sterm offset e1, rename_sterm offset e2)
    | SSeq (e1, e2) -> SSeq (rename_sterm offset e1, rename_sterm offset e2)
    | SMinus (e1, e2) -> SMinus (rename_sterm offset e1, rename_sterm offset e2)
    | SIfz (e1, e2, e3) -> SIfz (rename_sterm offset e1, rename_sterm offset e2, rename_sterm offset e3)

let rename_sym_map offset m =
    IntMap.map (fun info -> { sym_type = rename_typ offset info.sym_type }) m

let rename_eq offset (t1, t2) = (rename_typ offset t1, rename_typ offset t2)

let rename_prototerm offset s =
    { s with
      sterm = rename_sterm offset s.sterm;
      styp = rename_typ offset s.styp;
      sym_map = rename_sym_map offset s.sym_map;
      type_eqs = List.map (rename_eq offset) s.type_eqs;
      type_neqs = List.map (rename_eq offset) s.type_neqs;
      next_tvar = s.next_tvar + offset }

let rec rename_sym_sterm offset t =
    match t with
    | SBound (i, info) -> SBound (i, Option.map (fun (id, ty) -> (id + offset, ty)) info)
    | SFree id -> SFree (id + offset)
    | SLam (ty, body) -> SLam (ty, rename_sym_sterm offset body)
    | SApp (t1, t2) -> SApp (rename_sym_sterm offset t1, rename_sym_sterm offset t2)
    | SConst c -> SConst c
    | STyLam body -> STyLam (rename_sym_sterm offset body)
    | STyApp (e, ty) -> STyApp (rename_sym_sterm offset e, ty)
    | SMkRef e -> SMkRef (rename_sym_sterm offset e)
    | SDeref e -> SDeref (rename_sym_sterm offset e)
    | SAssign (e1, e2) -> SAssign (rename_sym_sterm offset e1, rename_sym_sterm offset e2)
    | SSeq (e1, e2) -> SSeq (rename_sym_sterm offset e1, rename_sym_sterm offset e2)
    | SMinus (e1, e2) -> SMinus (rename_sym_sterm offset e1, rename_sym_sterm offset e2)
    | SIfz (e1, e2, e3) -> SIfz (rename_sym_sterm offset e1, rename_sym_sterm offset e2, rename_sym_sterm offset e3)

let rename_sym_map_ids offset m =
    IntMap.fold (fun id info acc -> IntMap.add (id + offset) info acc) m IntMap.empty

let rename_sym_prototerm offset s =
    { s with
      sterm = rename_sym_sterm offset s.sterm;
      sym_map = rename_sym_map_ids offset s.sym_map;
      next_sym = s.next_sym + offset }

let rec shift_tyvar_sterm cutoff offset t =
    match t with
    | SBound (i, info) ->
        SBound (i, Option.map (fun (id, ty) -> (id, shift_tyvar cutoff offset ty)) info)
    | SFree _ -> t
    | SLam (ty, body) -> SLam (shift_tyvar cutoff offset ty, shift_tyvar_sterm cutoff offset body)
    | SApp (t1, t2) -> SApp (shift_tyvar_sterm cutoff offset t1, shift_tyvar_sterm cutoff offset t2)
    | SConst _ -> t
    | STyLam body -> STyLam (shift_tyvar_sterm (cutoff + 1) offset body)
    | STyApp (e, ty) -> STyApp (shift_tyvar_sterm cutoff offset e, shift_tyvar cutoff offset ty)
    | SMkRef e -> SMkRef (shift_tyvar_sterm cutoff offset e)
    | SDeref e -> SDeref (shift_tyvar_sterm cutoff offset e)
    | SAssign (e1, e2) -> SAssign (shift_tyvar_sterm cutoff offset e1, shift_tyvar_sterm cutoff offset e2)
    | SSeq (e1, e2) -> SSeq (shift_tyvar_sterm cutoff offset e1, shift_tyvar_sterm cutoff offset e2)
    | SMinus (e1, e2) -> SMinus (shift_tyvar_sterm cutoff offset e1, shift_tyvar_sterm cutoff offset e2)
    | SIfz (e1, e2, e3) ->
        SIfz (shift_tyvar_sterm cutoff offset e1,
              shift_tyvar_sterm cutoff offset e2,
              shift_tyvar_sterm cutoff offset e3)

let shift_tyvar_sym_map cutoff offset m =
    IntMap.map (fun info -> { sym_type = shift_tyvar cutoff offset info.sym_type }) m

let shift_tyvar_eq cutoff offset (t1, t2) =
    (shift_tyvar cutoff offset t1, shift_tyvar cutoff offset t2)

let shift_tyvar_prototerm cutoff offset s =
    { s with
      sterm = shift_tyvar_sterm cutoff offset s.sterm;
      styp = shift_tyvar cutoff offset s.styp;
      sym_map = shift_tyvar_sym_map cutoff offset s.sym_map;
      type_eqs = List.map (shift_tyvar_eq cutoff offset) s.type_eqs;
      type_neqs = List.map (shift_tyvar_eq cutoff offset) s.type_neqs }

let rec subst_typ i replacement t =
    match t with
    | Int | Unit | ListInt | TyVar _ -> t
    | TVar j -> if j = i then replacement else t
    | Arrow (t1, t2) -> Arrow (subst_typ i replacement t1, subst_typ i replacement t2)
    | Forall body -> Forall (subst_typ i replacement body)
    | Ref t -> Ref (subst_typ i replacement t)

let subst_eqs i replacement eqs =
    List.map (fun (t1, t2) -> (subst_typ i replacement t1, subst_typ i replacement t2)) eqs

let rec occurs i t =
    match t with
    | Int | Unit | ListInt | TyVar _ -> false
    | TVar j -> i = j
    | Arrow (t1, t2) -> occurs i t1 || occurs i t2
    | Forall body -> occurs i body
    | Ref t -> occurs i t

let rec unify eqs subst =
    match eqs with
    | [] -> Some subst
    | (Int, Int) :: rest -> unify rest subst
    | (Unit, Unit) :: rest -> unify rest subst
    | (ListInt, ListInt) :: rest -> unify rest subst
    | (TVar i, TVar j) :: rest when i = j -> unify rest subst
    | (TVar i, t) :: rest | (t, TVar i) :: rest ->
        if occurs i t then None else
        let subst' = List.map (fun (j, s) -> (j, subst_typ i t s)) subst in
        unify (subst_eqs i t rest) ((i, t) :: subst')
    | (Arrow (a1, b1), Arrow (a2, b2)) :: rest ->
        unify ((a1, a2) :: (b1, b2) :: rest) subst
    | (Ref t1, Ref t2) :: rest ->
        unify ((t1, t2) :: rest) subst
    | (TyVar i, TyVar j) :: rest ->
        if i = j then unify rest subst else None
    | (Forall t1, Forall t2) :: rest ->
        unify ((t1, t2) :: rest) subst
    | _ -> None

let rec apply_subst subst t =
    match subst with
    | [] -> t
    | (i, s) :: rest -> apply_subst rest (subst_typ i s t)

let rec apply_subst_sterm subst t =
    match t with
    | SBound (i, info) -> SBound (i, Option.map (fun (id, ty) -> (id, apply_subst subst ty)) info)
    | SFree id -> SFree id
    | SLam (ty, body) -> SLam (apply_subst subst ty, apply_subst_sterm subst body)
    | SApp (t1, t2) -> SApp (apply_subst_sterm subst t1, apply_subst_sterm subst t2)
    | SConst c -> SConst c
    | STyLam body -> STyLam (apply_subst_sterm subst body)
    | STyApp (e, ty) -> STyApp (apply_subst_sterm subst e, apply_subst subst ty)
    | SMkRef e -> SMkRef (apply_subst_sterm subst e)
    | SDeref e -> SDeref (apply_subst_sterm subst e)
    | SAssign (e1, e2) -> SAssign (apply_subst_sterm subst e1, apply_subst_sterm subst e2)
    | SSeq (e1, e2) -> SSeq (apply_subst_sterm subst e1, apply_subst_sterm subst e2)
    | SMinus (e1, e2) -> SMinus (apply_subst_sterm subst e1, apply_subst_sterm subst e2)
    | SIfz (e1, e2, e3) -> SIfz (apply_subst_sterm subst e1, apply_subst_sterm subst e2, apply_subst_sterm subst e3)

let apply_subst_sym_map subst m =
    IntMap.map (fun info -> { sym_type = apply_subst subst info.sym_type }) m

let apply_subst_prototerm subst s =
    { s with
      sterm = apply_subst_sterm subst s.sterm;
      styp = apply_subst subst s.styp;
      sym_map = apply_subst_sym_map subst s.sym_map;
      type_eqs = [];
      type_neqs = List.map (fun (t1, t2) -> (apply_subst subst t1, apply_subst subst t2)) s.type_neqs }

let solve_prototerm s =
    match unify s.type_eqs [] with
    | None -> None
    | Some subst -> Some (apply_subst_prototerm subst s)

let is_closed_prototerm s = IntMap.is_empty s.sym_map

let rec subst_free_with_bound id sym_type depth t =
    match t with
    | SBound (i, info) -> SBound (i, info)
    | SFree id' -> if id' = id then SBound (depth, Some (id, sym_type)) else SFree id'
    | SLam (ty, body) -> SLam (ty, subst_free_with_bound id sym_type (depth + 1) body)
    | SApp (t1, t2) -> SApp (subst_free_with_bound id sym_type depth t1, subst_free_with_bound id sym_type depth t2)
    | SConst c -> SConst c
    | STyLam body -> STyLam (subst_free_with_bound id sym_type depth body)
    | STyApp (e, ty) -> STyApp (subst_free_with_bound id sym_type depth e, ty)
    | SMkRef e -> SMkRef (subst_free_with_bound id sym_type depth e)
    | SDeref e -> SDeref (subst_free_with_bound id sym_type depth e)
    | SAssign (e1, e2) -> SAssign (subst_free_with_bound id sym_type depth e1, subst_free_with_bound id sym_type depth e2)
    | SSeq (e1, e2) -> SSeq (subst_free_with_bound id sym_type depth e1, subst_free_with_bound id sym_type depth e2)
    | SMinus (e1, e2) -> SMinus (subst_free_with_bound id sym_type depth e1, subst_free_with_bound id sym_type depth e2)
    | SIfz (e1, e2, e3) -> SIfz (subst_free_with_bound id sym_type depth e1, subst_free_with_bound id sym_type depth e2, subst_free_with_bound id sym_type depth e3)

let make_var_prototerm () =
    let alpha = TVar 0 in
    { sterm = SFree 0;
      styp = alpha;
      sym_map = IntMap.singleton 0 { sym_type = alpha };
      type_eqs = [];
      type_neqs = [];
      next_tvar = 1;
      next_sym = 1 }

let make_const_prototerm c =
    { sterm = SConst c;
      styp = const_type_of c;
      sym_map = IntMap.empty;
      type_eqs = [];
      type_neqs = [];
      next_tvar = 0;
      next_sym = 0 }

let merge2 s1 s2 =
    let s2' = rename_prototerm s1.next_tvar s2 in
    let s2'' = rename_sym_prototerm s1.next_sym s2' in
    let merged = IntMap.union (fun _ a _ -> Some a) s1.sym_map s2''.sym_map in
    (s2'', merged)

let merge3 s1 s2 s3 =
    let (s2'', merged12) = merge2 s1 s2 in
    let s3' = rename_prototerm s2''.next_tvar s3 in
    let s3'' = rename_sym_prototerm s2''.next_sym s3' in
    let merged = IntMap.union (fun _ a _ -> Some a) merged12 s3''.sym_map in
    (s2'', s3'', merged)

let rec sterm_to_term_with_bindings t =
    match t with
    | SBound (i, info) ->
        let bindings = match info with
            | Some (sym_id, binding_type) -> [{ sym_id; de_bruijn_idx = i; binding_type }]
            | None -> [] in
        (Var i, bindings)
    | SFree _ -> failwith "Cannot concretize: proto-term has free variables"
    | SLam (ty, body) ->
        let (body', bindings) = sterm_to_term_with_bindings body in
        (Lam (ty, body'), bindings)
    | SApp (t1, t2) ->
        let (t1', b1) = sterm_to_term_with_bindings t1 in
        let (t2', b2) = sterm_to_term_with_bindings t2 in
        (App (t1', t2'), b1 @ b2)
    | SConst c -> (Const c, [])
    | STyLam body ->
        let (body', bindings) = sterm_to_term_with_bindings body in
        (TyLam body', bindings)
    | STyApp (e, ty) ->
        let (e', bindings) = sterm_to_term_with_bindings e in
        (TyApp (e', ty), bindings)
    | SMkRef e ->
        let (e', bindings) = sterm_to_term_with_bindings e in
        (MkRef e', bindings)
    | SDeref e ->
        let (e', bindings) = sterm_to_term_with_bindings e in
        (Deref e', bindings)
    | SAssign (e1, e2) ->
        let (e1', b1) = sterm_to_term_with_bindings e1 in
        let (e2', b2) = sterm_to_term_with_bindings e2 in
        (Assign (e1', e2'), b1 @ b2)
    | SSeq (e1, e2) ->
        let (e1', b1) = sterm_to_term_with_bindings e1 in
        let (e2', b2) = sterm_to_term_with_bindings e2 in
        (Seq (e1', e2'), b1 @ b2)
    | SMinus (e1, e2) ->
        let (e1', b1) = sterm_to_term_with_bindings e1 in
        let (e2', b2) = sterm_to_term_with_bindings e2 in
        (Minus (e1', e2'), b1 @ b2)
    | SIfz (e1, e2, e3) ->
        let (e1', b1) = sterm_to_term_with_bindings e1 in
        let (e2', b2) = sterm_to_term_with_bindings e2 in
        let (e3', b3) = sterm_to_term_with_bindings e3 in
        (Ifz (e1', e2', e3'), b1 @ b2 @ b3)

let concretize_prototerm s =
    if not (is_closed_prototerm s) then failwith "Cannot concretize: proto-term has free symbolic variables"
    else
    let (term, bindings) = sterm_to_term_with_bindings s.sterm in
    { term; typ = s.styp; bindings }

let base_atoms ~no_lists = if no_lists then [Int; Unit] else [Int; Unit; ListInt]

let rec types_up_to_depth_with_tyvars ~no_lists n_tyvars d =
    let base = base_atoms ~no_lists in
    let tyvar_types = List.init n_tyvars (fun i -> TyVar i) in
    if d <= 0 then base @ tyvar_types
    else
    let smaller = types_up_to_depth_with_tyvars ~no_lists n_tyvars (d - 1) in
    let arrows = List.concat_map (fun t1 ->
        List.map (fun t2 -> Arrow (t1, t2)) smaller) smaller in
    let refs = List.map (fun t -> Ref t) smaller in
    let forall_bodies = types_up_to_depth_with_tyvars ~no_lists (n_tyvars + 1) (d - 1) in
    let foralls = List.map (fun body -> Forall body) forall_bodies in
    base @ tyvar_types @ arrows @ refs @ foralls

let types_up_to_depth ~no_lists d = types_up_to_depth_with_tyvars ~no_lists 0 d

let rec types_at_depth_with_tyvars ~no_lists n d =
    let base = base_atoms ~no_lists in
    if d <= 0 then base @ List.init n (fun i -> TyVar i)
    else
    let exact = types_at_depth_with_tyvars ~no_lists n (d - 1) in
    let upto1 = types_up_to_depth_with_tyvars ~no_lists n (d - 1) in
    let below = if d >= 2 then types_up_to_depth_with_tyvars ~no_lists n (d - 2) else [] in
    List.concat_map (fun a -> List.map (fun b -> Arrow (a, b)) upto1) exact
    @ List.concat_map (fun a -> List.map (fun b -> Arrow (a, b)) exact) below
    @ List.map (fun t -> Ref t) exact
    @ List.map (fun body -> Forall body) (types_at_depth_with_tyvars ~no_lists (n + 1) (d - 1))

let all_types_with_tyvars ~no_lists n : typ Seq.t =
    Seq.concat_map (fun d -> List.to_seq (types_at_depth_with_tyvars ~no_lists n d))
        (Helper.nats 0)

let all_types = all_types_with_tyvars ~no_lists:false 0
let all_types_no_lists = all_types_with_tyvars ~no_lists:true 0

let type_basis (config : config) =
    match config.type_depth_bound with
    | None -> if config.no_lists then all_types_no_lists else all_types
    | Some d -> List.to_seq (types_up_to_depth ~no_lists:config.no_lists d)

let neq_filter_bound = 100_000

let neqs_violated neqs = List.exists (fun (t1, t2) -> t1 = t2) neqs

let rec tvars_in_term t =
    match t with
    | Var _ | Const _ -> IntSet.empty
    | Lam (ty, body) -> IntSet.union (tvars_in_typ ty) (tvars_in_term body)
    | App (t1, t2) -> IntSet.union (tvars_in_term t1) (tvars_in_term t2)
    | TyLam body -> tvars_in_term body
    | TyApp (e, ty) -> IntSet.union (tvars_in_term e) (tvars_in_typ ty)
    | MkRef e -> tvars_in_term e
    | Deref e -> tvars_in_term e
    | Assign (e1, e2) -> IntSet.union (tvars_in_term e1) (tvars_in_term e2)
    | Seq (e1, e2) -> IntSet.union (tvars_in_term e1) (tvars_in_term e2)
    | Minus (e1, e2) -> IntSet.union (tvars_in_term e1) (tvars_in_term e2)
    | Ifz (e1, e2, e3) ->
        IntSet.union (tvars_in_term e1) @@
        IntSet.union (tvars_in_term e2) (tvars_in_term e3)

let tvars_in_fact f = IntSet.union (tvars_in_typ f.typ) (tvars_in_term f.term)

let rec apply_subst_term subst t =
    match t with
    | Var i -> Var i
    | Lam (ty, body) -> Lam (apply_subst subst ty, apply_subst_term subst body)
    | App (t1, t2) -> App (apply_subst_term subst t1, apply_subst_term subst t2)
    | Const c -> Const c
    | TyLam body -> TyLam (apply_subst_term subst body)
    | TyApp (e, ty) -> TyApp (apply_subst_term subst e, apply_subst subst ty)
    | MkRef e -> MkRef (apply_subst_term subst e)
    | Deref e -> Deref (apply_subst_term subst e)
    | Assign (e1, e2) -> Assign (apply_subst_term subst e1, apply_subst_term subst e2)
    | Seq (e1, e2) -> Seq (apply_subst_term subst e1, apply_subst_term subst e2)
    | Minus (e1, e2) -> Minus (apply_subst_term subst e1, apply_subst_term subst e2)
    | Ifz (e1, e2, e3) -> Ifz (apply_subst_term subst e1, apply_subst_term subst e2, apply_subst_term subst e3)

let apply_subst_binding subst b =
    { b with binding_type = apply_subst subst b.binding_type }

let apply_subst_fact subst f =
    { term = apply_subst_term subst f.term;
      typ = apply_subst subst f.typ;
      bindings = List.map (apply_subst_binding subst) f.bindings }

type constr_head = [ `Arrow | `Ref | `Forall ]

let constr_view (t : typ) : [ `TVar of int | `Node of constr_head * typ list | `Atom ] =
    match t with
    | TVar i -> `TVar i
    | Arrow (a, b) -> `Node (`Arrow, [a; b])
    | Ref u -> `Node (`Ref, [u])
    | Forall u -> `Node (`Forall, [u])
    | Int | Unit | ListInt | TyVar _ -> `Atom

let rec constr_deep_fallback k = if k <= 0 then Ref Int else Ref (constr_deep_fallback (k - 1))

let rec constr_tvar_occurs v t =
    match constr_view t with
    | `TVar j -> j = v
    | `Node (_, cs) -> List.exists (constr_tvar_occurs v) cs
    | `Atom -> false

let rec constr_is_ground t =
    match constr_view t with
    | `TVar _ -> false
    | `Node (_, cs) -> List.for_all constr_is_ground cs
    | `Atom -> true

type ndecision =
    | DDiff
    | DIdent
    | DEdge of int * int
    | DForbidVal of int * typ
    | DForbidHead of int * constr_head

let rec align_neq t1 t2 =
    if t1 = t2 then DIdent
    else match constr_view t1, constr_view t2 with
        | `TVar v, `TVar w -> DEdge (v, w)
        | `TVar v, _ -> tvar_side v t2
        | _, `TVar v -> tvar_side v t1
        | `Node (h1, cs1), `Node (h2, cs2) ->
            if h1 = h2 && List.length cs1 = List.length cs2
            then combine_neq (List.map2 align_neq cs1 cs2)
            else DDiff
        | _ -> DDiff
and tvar_side v t =
    if constr_tvar_occurs v t then DDiff
    else if constr_is_ground t then DForbidVal (v, t)
    else (match constr_view t with
          | `Node (h, _) -> DForbidHead (v, h)
          | _ -> DDiff)
and combine_neq ds =
    if List.mem DDiff ds then DDiff
    else match List.find_opt
                 (function DEdge _ | DForbidVal _ | DForbidHead _ -> true | _ -> false) ds with
        | Some d -> d
        | None -> DIdent

let constraints_of_neqs neqs =
    List.fold_left (fun (edges, fval, fhead, unsat) (t1, t2) ->
        match align_neq t1 t2 with
        | DDiff -> (edges, fval, fhead, unsat)
        | DIdent -> (edges, fval, fhead, true)
        | DEdge (v, w) -> ((v, w) :: edges, fval, fhead, unsat)
        | DForbidVal (v, c) -> (edges, (v, c) :: fval, fhead, unsat)
        | DForbidHead (v, h) -> (edges, fval, (v, h) :: fhead, unsat)
    ) ([], [], [], false) neqs

let head_matches h t = match h, constr_view t with
    | `Arrow, `Node (`Arrow, _) -> true
    | `Ref, `Node (`Ref, _) -> true
    | `Forall, `Node (`Forall, _) -> true
    | _ -> false

let colour_tvars tvars (edges, fval, fhead, _) palette =
    let adj = Hashtbl.create 16 in
    let add a b =
        Hashtbl.replace adj a (b :: (try Hashtbl.find adj a with Not_found -> [])) in
    List.iter (fun (v, w) -> add v w; add w v) edges;
    let assign = Hashtbl.create 16 in
    let head_ok v t =
        List.for_all (fun (v', h) -> v' <> v || not (head_matches h t)) fhead in
    List.iter (fun v ->
        let nbr = try Hashtbl.find adj v with Not_found -> [] in
        let nbr_colours = List.filter_map (Hashtbl.find_opt assign) nbr in
        let bad t = List.exists (fun c -> c = t) nbr_colours
                    || List.exists (fun (v', c) -> v' = v && c = t) fval
                    || not (head_ok v t) in
        let chosen =
            match List.find_opt (fun t -> not (bad t)) palette with
            | Some t -> t
            | None ->
                let rec pick k = let t = constr_deep_fallback k in if bad t then pick (k + 1) else t in
                pick 0 in
        Hashtbl.replace assign v chosen
    ) tvars;
    List.map (fun v -> (v, Hashtbl.find assign v)) tvars

let constr_instantiate ~basis neqs (fact : fact) tvars ~fallback : fact Seq.t =
    if neqs_violated neqs then Seq.empty
    else
    let cons = constraints_of_neqs neqs in
    let (_, _, _, unsat) = cons in
    if unsat then Seq.empty
    else
    let palette0 = basis |> Seq.take 64 |> List.of_seq in
    let n = max 1 (List.length palette0) in
    let mk rot =
        let subst = colour_tvars tvars cons (Helper.rotate_list rot palette0) in
        let neqs' = List.map (fun (t1, t2) ->
            (apply_subst subst t1, apply_subst subst t2)) neqs in
        if neqs_violated neqs' then None
        else Some (apply_subst_fact subst fact) in
    match mk 0 with
    | None -> fallback ()
    | Some head ->
        let rec gen rot seen () =
            if rot >= n then Seq.Nil
            else match mk rot with
                | Some f when not (List.mem f seen) -> Seq.Cons (f, gen (rot + 1) (f :: seen))
                | _ -> gen (rot + 1) seen () in
        fun () -> Seq.Cons (head, gen 1 [head])

let instantiate_prototerm ~search_budget config s : fact Seq.t =
    match solve_prototerm s with
    | None -> Seq.empty
    | Some solved ->
        if not (is_closed_prototerm solved) then Seq.empty else
        if neqs_violated solved.type_neqs then Seq.empty else
        let fact = concretize_prototerm solved in
        let tvars = IntSet.elements @@ tvars_in_fact fact in
        if tvars = [] then Seq.return fact
        else if config.simple_types then
            let subst = List.map (fun v -> (v, Int)) tvars in
            let inst = apply_subst_fact subst fact in
            let neqs' = List.rev_map (fun (t1, t2) -> (apply_subst subst t1, apply_subst subst t2)) solved.type_neqs in
            if neqs_violated neqs' then Seq.empty else Seq.return inst
        else
            let k = List.length tvars in
            let products = Helper.fair_product (type_basis config) k in
            if solved.type_neqs = [] then
                Seq.map (fun ts -> apply_subst_fact (List.combine tvars ts) fact) products
            else
                let enumerate bound =
                    products
                    |> Seq.take bound
                    |> Seq.filter_map (fun ts ->
                        let subst = List.combine tvars ts in
                        let neqs' = List.rev_map (fun (t1, t2) ->
                            (apply_subst subst t1, apply_subst subst t2)) solved.type_neqs in
                        if neqs_violated neqs' then None
                        else Some (apply_subst_fact subst fact)) in
                let basis = if config.no_lists then all_types_no_lists else all_types in
                (match search_budget with
                 | Some b ->
                     constr_instantiate ~basis solved.type_neqs fact tvars
                         ~fallback:(fun () -> enumerate b)
                 | None -> enumerate neq_filter_bound)

let close_prototerm s =
    if IntMap.is_empty s.sym_map then []
    else
    let sorted =
        List.sort (fun (a, _) (b, _) -> compare a b) (IntMap.bindings s.sym_map) in
    let closed = List.fold_left (fun acc (id, info) ->
        let new_sterm = subst_free_with_bound id info.sym_type 0 acc.sterm in
        { acc with
          sterm = SLam (info.sym_type, new_sterm);
          styp = Arrow (info.sym_type, acc.styp);
          sym_map = IntMap.remove id acc.sym_map }) s sorted in
    [closed]

let auto_close_if_needed config s =
    if config.auto_close && not (is_closed_prototerm s) then
        match close_prototerm s with
        | [closed] -> closed
        | _ -> s
    else s

let concretize ~search_budget config s =
    instantiate_prototerm ~search_budget config (auto_close_if_needed config s)
