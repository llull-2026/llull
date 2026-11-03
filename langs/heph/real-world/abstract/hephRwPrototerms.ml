open HephRwPrograms

type config = {
    auto_close     : bool;
    max_tvars      : int;
    max_type_depth : int;
    assignment_cap : int;
    max_identical_classes : int;
    rich_methods   : bool;
    resolve_method_sigs : bool;
    class_sampling : bool;
    scoped_bounds  : bool;
    approx_field_reads : bool;
    multi_wildcards : bool;
    tvar_wildcard_fields : bool;
    explicit_news  : bool;
    generic_methods : bool;
    mutate_return  : bool;
    randomize_breaks : bool;
}

type proto_term =
    | SFree of int
    | SBound of int
    | SNew of heph_type * proto_term list
    | SFieldAccess of proto_term * field_label
    | SMethodInvoke of proto_term * method_label * proto_term list
    | SLambda of heph_type * proto_term
    | SCond of proto_term * proto_term * proto_term
    | SNull of heph_type

let rec string_of_sterm = function
    | SFree id -> "x" ^ string_of_int id
    | SBound i -> "#" ^ string_of_int i
    | SNew (ty, []) -> "new " ^ string_of_type ty ^ "()"
    | SNull ty -> "(" ^ string_of_type ty ^ ") null"
    | SNew (ty, args) ->
        "new " ^ string_of_type ty ^ "(" ^
        String.concat ", " (List.map string_of_sterm args) ^ ")"
    | SFieldAccess (e, fl) -> string_of_sterm_recv e ^ "." ^ fl_name fl
    | SMethodInvoke (e, ml, []) -> string_of_sterm_recv e ^ "." ^ ml_name ml ^ "()"
    | SMethodInvoke (e, ml, args) ->
        string_of_sterm_recv e ^ "." ^ ml_name ml ^ "(" ^
        String.concat ", " (List.map string_of_sterm args) ^ ")"
    | SLambda (t, body) ->
        "\\:" ^ string_of_type t ^ ". " ^ string_of_sterm body
    | SCond (c, t, e) ->
        "(" ^ string_of_sterm c ^ " ? " ^ string_of_sterm t ^ " : "
        ^ string_of_sterm e ^ ")"

and string_of_sterm_recv t =
    match t with
    | SNew _ | SLambda _ | SNull _ -> "(" ^ string_of_sterm t ^ ")"
    | _ -> string_of_sterm t

type demand =
    | NeedField of heph_type * field_label * heph_type
    | NeedMethod of heph_type * method_label * heph_type list * heph_type
    | Subtype of heph_type * heph_type
    | FieldCount of heph_type * int
    | TparamBound of class_ref * int * heph_type

type label_kind = LField | LMethod
type label_neq = label_kind * int * int

type sym_info = { sym_type : heph_type }

type expr_proto_term = {
    sterm : proto_term;
    styp : heph_type;
    sym_map : sym_info IntMap.t;
    demands : demand list;
    label_neqs : label_neq list;
    next_tvar : int;
    next_sym : int;
    next_fl : int;
    next_ml : int;
}

let rec field_labels_in_sterm = function
    | SFree _ | SBound _ | SNull _ -> IntSet.empty
    | SNew (_, args) ->
        List.fold_left (fun acc a -> IntSet.union acc (field_labels_in_sterm a))
            IntSet.empty args
    | SFieldAccess (e, fl) -> IntSet.add fl (field_labels_in_sterm e)
    | SMethodInvoke (e, _, args) ->
        List.fold_left (fun acc a -> IntSet.union acc (field_labels_in_sterm a))
            (field_labels_in_sterm e) args
    | SLambda (_, body) -> field_labels_in_sterm body
    | SCond (c, t, e) ->
        IntSet.union (field_labels_in_sterm c)
            (IntSet.union (field_labels_in_sterm t) (field_labels_in_sterm e))

let field_labels_in_demands ds =
    List.fold_left (fun acc d -> match d with
        | NeedField (_, fl, _) -> IntSet.add fl acc
        | _ -> acc
    ) IntSet.empty ds

let field_labels_in_proto_term s =
    IntSet.union (field_labels_in_sterm s.sterm) (field_labels_in_demands s.demands)

let rec rename_type off_tv = function
    | TVar i -> TVar (i + off_tv)
    | t -> map_type_children (rename_type off_tv) t

let rename_demand off_tv off_fl off_ml = function
    | NeedField (r, fl, res) ->
        NeedField (rename_type off_tv r, fl + off_fl, rename_type off_tv res)
    | NeedMethod (r, ml, ps, ret) ->
        NeedMethod (rename_type off_tv r, ml + off_ml,
                    List.map (rename_type off_tv) ps, rename_type off_tv ret)
    | Subtype (a, b) -> Subtype (rename_type off_tv a, rename_type off_tv b)
    | FieldCount (t, k) -> FieldCount (rename_type off_tv t, k)
    | TparamBound (cr, i, b) -> TparamBound (cr, i, rename_type off_tv b)

let rename_label_neq off_fl off_ml = function
    | (LField, l1, l2) -> (LField, l1 + off_fl, l2 + off_fl)
    | (LMethod, l1, l2) -> (LMethod, l1 + off_ml, l2 + off_ml)

let rec rename_sterm off_tv off_sym off_fl off_ml = function
    | SFree id -> SFree (id + off_sym)
    | SBound _ as t -> t
    | SNull ty -> SNull (rename_type off_tv ty)
    | SNew (ty, args) ->
        SNew (rename_type off_tv ty,
              List.map (rename_sterm off_tv off_sym off_fl off_ml) args)
    | SFieldAccess (e, fl) ->
        SFieldAccess (rename_sterm off_tv off_sym off_fl off_ml e, fl + off_fl)
    | SMethodInvoke (e, ml, args) ->
        SMethodInvoke (rename_sterm off_tv off_sym off_fl off_ml e,
                       ml + off_ml,
                       List.map (rename_sterm off_tv off_sym off_fl off_ml) args)
    | SLambda (ty, body) ->
        SLambda (rename_type off_tv ty,
                 rename_sterm off_tv off_sym off_fl off_ml body)
    | SCond (c, t, e) ->
        SCond (rename_sterm off_tv off_sym off_fl off_ml c,
               rename_sterm off_tv off_sym off_fl off_ml t,
               rename_sterm off_tv off_sym off_fl off_ml e)

let rename_sym_map off_sym off_tv m =
    IntMap.fold (fun id info acc ->
        IntMap.add (id + off_sym)
            { sym_type = rename_type off_tv info.sym_type } acc
    ) m IntMap.empty

let rename_proto_term off_tv off_sym off_fl off_ml s =
    { sterm = rename_sterm off_tv off_sym off_fl off_ml s.sterm;
      styp = rename_type off_tv s.styp;
      sym_map = rename_sym_map off_sym off_tv s.sym_map;
      demands = List.map (rename_demand off_tv off_fl off_ml) s.demands;
      label_neqs = List.map (rename_label_neq off_fl off_ml) s.label_neqs;
      next_tvar = s.next_tvar + off_tv;
      next_sym = s.next_sym + off_sym;
      next_fl = s.next_fl + off_fl;
      next_ml = s.next_ml + off_ml }

let merge_proto_term_contexts proto_terms =
    match proto_terms with
    | [] -> ([], IntMap.empty, [], [], 0, 0, 0, 0)
    | first :: rest ->
        let rec go acc sm ds neqs nt nsy nfl nml = function
            | [] -> (List.rev acc, sm, ds, neqs, nt, nsy, nfl, nml)
            | s :: tl ->
                let s' = rename_proto_term nt nsy nfl nml s in
                let sm' = IntMap.union (fun _ a _ -> Some a) sm s'.sym_map in
                let ds' = ds @ s'.demands in
                let neqs' = neqs @ s'.label_neqs in
                go (s' :: acc) sm' ds' neqs'
                    s'.next_tvar s'.next_sym s'.next_fl s'.next_ml tl
        in
        go [first] first.sym_map first.demands first.label_neqs
            first.next_tvar first.next_sym first.next_fl first.next_ml rest

let rec subst_sfree j i = function
    | SFree id -> SFree (if id = j then i else id)
    | SBound _ as t -> t
    | SNull _ as t -> t
    | SNew (ty, args) -> SNew (ty, List.map (subst_sfree j i) args)
    | SFieldAccess (e, fl) -> SFieldAccess (subst_sfree j i e, fl)
    | SMethodInvoke (e, ml, args) ->
        SMethodInvoke (subst_sfree j i e, ml, List.map (subst_sfree j i) args)
    | SLambda (ty, body) -> SLambda (ty, subst_sfree j i body)
    | SCond (c, t, e) ->
        SCond (subst_sfree j i c, subst_sfree j i t, subst_sfree j i e)

let rec subst_tvar_type old_id new_id = function
    | TVar i when i = old_id -> TVar new_id
    | t -> map_type_children (subst_tvar_type old_id new_id) t

let rec subst_tvar_sterm old_id new_id = function
    | SFree _ | SBound _ as t -> t
    | SNull ty -> SNull (subst_tvar_type old_id new_id ty)
    | SNew (ty, args) ->
        SNew (subst_tvar_type old_id new_id ty,
              List.map (subst_tvar_sterm old_id new_id) args)
    | SFieldAccess (e, fl) -> SFieldAccess (subst_tvar_sterm old_id new_id e, fl)
    | SMethodInvoke (e, ml, args) ->
        SMethodInvoke (subst_tvar_sterm old_id new_id e, ml,
                       List.map (subst_tvar_sterm old_id new_id) args)
    | SLambda (ty, body) ->
        SLambda (subst_tvar_type old_id new_id ty,
                 subst_tvar_sterm old_id new_id body)
    | SCond (c, t, e) ->
        SCond (subst_tvar_sterm old_id new_id c,
               subst_tvar_sterm old_id new_id t,
               subst_tvar_sterm old_id new_id e)

let subst_tvar_demand old_id new_id = function
    | NeedField (r, fl, res) ->
        NeedField (subst_tvar_type old_id new_id r, fl,
                   subst_tvar_type old_id new_id res)
    | NeedMethod (r, ml, ps, ret) ->
        NeedMethod (subst_tvar_type old_id new_id r, ml,
                    List.map (subst_tvar_type old_id new_id) ps,
                    subst_tvar_type old_id new_id ret)
    | Subtype (a, b) ->
        Subtype (subst_tvar_type old_id new_id a, subst_tvar_type old_id new_id b)
    | FieldCount (t, k) -> FieldCount (subst_tvar_type old_id new_id t, k)
    | TparamBound (cr, i, b) ->
        TparamBound (cr, i, subst_tvar_type old_id new_id b)

let rec subst_tvar_with_type_in_type old_id repl = function
    | TVar i when i = old_id -> repl
    | t -> map_type_children (subst_tvar_with_type_in_type old_id repl) t

let rec subst_tvar_with_type_in_sterm old_id repl = function
    | SFree _ | SBound _ as t -> t
    | SNull ty -> SNull (subst_tvar_with_type_in_type old_id repl ty)
    | SNew (ty, args) ->
        SNew (subst_tvar_with_type_in_type old_id repl ty,
              List.map (subst_tvar_with_type_in_sterm old_id repl) args)
    | SFieldAccess (e, fl) ->
        SFieldAccess (subst_tvar_with_type_in_sterm old_id repl e, fl)
    | SMethodInvoke (e, ml, args) ->
        SMethodInvoke (subst_tvar_with_type_in_sterm old_id repl e, ml,
                       List.map (subst_tvar_with_type_in_sterm old_id repl) args)
    | SLambda (ty, body) ->
        SLambda (subst_tvar_with_type_in_type old_id repl ty,
                 subst_tvar_with_type_in_sterm old_id repl body)
    | SCond (c, t, e) ->
        SCond (subst_tvar_with_type_in_sterm old_id repl c,
               subst_tvar_with_type_in_sterm old_id repl t,
               subst_tvar_with_type_in_sterm old_id repl e)

let subst_tvar_with_type_in_demand old_id repl d =
    let st = subst_tvar_with_type_in_type old_id repl in
    match d with
    | NeedField (r, fl, res) -> NeedField (st r, fl, st res)
    | NeedMethod (r, ml, ps, ret) ->
        NeedMethod (st r, ml, List.map st ps, st ret)
    | Subtype (a, b) -> Subtype (st a, st b)
    | FieldCount (t, k) -> FieldCount (st t, k)
    | TparamBound (cr, i, b) -> TparamBound (cr, i, st b)

let subst_tvar_with_type_in_proto_term old_id repl s =
    { s with
      sterm = subst_tvar_with_type_in_sterm old_id repl s.sterm;
      styp = subst_tvar_with_type_in_type old_id repl s.styp;
      sym_map = IntMap.map (fun info ->
          { sym_type = subst_tvar_with_type_in_type old_id repl info.sym_type }
      ) s.sym_map;
      demands = List.map (subst_tvar_with_type_in_demand old_id repl) s.demands }

let rec method_labels_in_sterm = function
    | SFree _ | SBound _ | SNull _ -> IntSet.empty
    | SNew (_, args) ->
        List.fold_left (fun acc a -> IntSet.union acc (method_labels_in_sterm a))
            IntSet.empty args
    | SFieldAccess (e, _) -> method_labels_in_sterm e
    | SMethodInvoke (e, ml, args) ->
        List.fold_left (fun acc a -> IntSet.union acc (method_labels_in_sterm a))
            (IntSet.add ml (method_labels_in_sterm e)) args
    | SLambda (_, body) -> method_labels_in_sterm body
    | SCond (c, t, e) ->
        IntSet.union (method_labels_in_sterm c)
            (IntSet.union (method_labels_in_sterm t) (method_labels_in_sterm e))

let method_labels_in_demands ds =
    List.fold_left (fun acc d -> match d with
        | NeedMethod (_, ml, _, _) -> IntSet.add ml acc
        | _ -> acc
    ) IntSet.empty ds

let method_labels_in_proto_term s =
    IntSet.union (method_labels_in_sterm s.sterm) (method_labels_in_demands s.demands)

let make_var_proto_term () =
    { sterm = SFree 0;
      styp = TVar 0;
      sym_map = IntMap.singleton 0 { sym_type = TVar 0 };
      demands = [];
      label_neqs = [];
      next_tvar = 1;
      next_sym = 1;
      next_fl = 0;
      next_ml = 0 }

let make_prelude_new name =
    { sterm = SNew (TyClass (Prelude name, []), []);
      styp = TyClass (Prelude name, []);
      sym_map = IntMap.empty;
      demands = [];
      label_neqs = [];
      next_tvar = 0;
      next_sym = 0;
      next_fl = 0;
      next_ml = 0 }

let make_null () =
    { sterm = SNull (TVar 0);
      styp = TVar 0;
      sym_map = IntMap.empty;
      demands = [];
      label_neqs = [];
      next_tvar = 1;
      next_sym = 0;
      next_fl = 0;
      next_ml = 0 }

let make_new0 () =
    { sterm = SNew (TVar 0, []);
      styp = TVar 0;
      sym_map = IntMap.empty;
      demands = [FieldCount (TVar 0, 0)];
      label_neqs = [];
      next_tvar = 1;
      next_sym = 0;
      next_fl = 0;
      next_ml = 0 }

let try_new_k args =
    let k = List.length args in
    let (args', sm, demands, neqs, nt, nsy, nfl, nml) = merge_proto_term_contexts args in
    let target_tv = nt in
    let target = TVar target_tv in
    let ft_tvs = List.init k (fun i -> target_tv + 1 + i) in
    let ft_types = List.map (fun i -> TVar i) ft_tvs in
    let fcount = FieldCount (target, k) in
    let subtype_demands = List.map2 (fun a ft ->
        Subtype (a.styp, ft)
    ) args' ft_types in
    let field_demands = List.mapi (fun i ft ->
        NeedField (target, nfl + i, ft)
    ) ft_types in
    let field_neqs = List.concat_map (fun i ->
        List.filter_map (fun j ->
            if j > i then Some (LField, nfl + i, nfl + j) else None
        ) (List.init k Fun.id)
    ) (List.init k Fun.id) in
    [{ sterm = SNew (target, List.map (fun a -> a.sterm) args');
       styp = target;
       sym_map = sm;
       demands = fcount :: subtype_demands @ field_demands @ demands;
       label_neqs = field_neqs @ neqs;
       next_tvar = target_tv + 1 + k;
       next_sym = nsy;
       next_fl = nfl + k;
       next_ml = nml }]

let try_field_access s =
    let existing_fls = IntSet.elements (field_labels_in_proto_term s) in
    let result_tv = s.next_tvar in
    let make_variant fl nfl neqs =
        { sterm = SFieldAccess (s.sterm, fl);
          styp = TVar result_tv;
          sym_map = s.sym_map;
          demands = NeedField (s.styp, fl, TVar result_tv) :: s.demands;
          label_neqs = neqs;
          next_tvar = result_tv + 1;
          next_sym = s.next_sym;
          next_fl = nfl;
          next_ml = s.next_ml }
    in
    let reuse_variants = List.map (fun fl ->
        make_variant fl s.next_fl s.label_neqs
    ) existing_fls in
    let fresh_fl = s.next_fl in
    let fresh_neqs = List.map (fun fl -> (LField, fresh_fl, fl)) existing_fls in
    let fresh_variant = make_variant fresh_fl (fresh_fl + 1) (fresh_neqs @ s.label_neqs) in
    reuse_variants @ [fresh_variant]

let try_contract s =
    let syms = IntMap.bindings s.sym_map in
    if List.length syms < 2 then []
    else
        List.concat_map (fun (i, info_i) ->
            List.filter_map (fun (j, info_j) ->
                if j <= i then None
                else match info_i.sym_type, info_j.sym_type with
                | TVar ti, TVar tj ->
                    let sterm' = subst_sfree j i s.sterm in
                    let sym_map' = IntMap.remove j s.sym_map in
                    if ti = tj then
                        Some { s with sterm = sterm'; sym_map = sym_map' }
                    else
                        let demands' = List.map (subst_tvar_demand tj ti) s.demands in
                        let sterm'' = subst_tvar_sterm tj ti sterm' in
                        Some { s with
                               sterm = sterm'';
                               styp = subst_tvar_type tj ti s.styp;
                               sym_map = IntMap.map (fun info ->
                                   { sym_type = subst_tvar_type tj ti info.sym_type }
                               ) sym_map';
                               demands = demands' }
                | _ -> None
            ) syms
        ) syms

let rec subst_sfree_with_sbound id depth = function
    | SFree j -> if j = id then SBound depth else SFree j
    | SBound _ as t -> t
    | SNull _ as t -> t
    | SNew (ty, args) ->
        SNew (ty, List.map (subst_sfree_with_sbound id depth) args)
    | SFieldAccess (e, fl) ->
        SFieldAccess (subst_sfree_with_sbound id depth e, fl)
    | SMethodInvoke (e, ml, args) ->
        SMethodInvoke (subst_sfree_with_sbound id depth e, ml,
                       List.map (subst_sfree_with_sbound id depth) args)
    | SLambda (ty, body) ->
        SLambda (ty, subst_sfree_with_sbound id (depth + 1) body)
    | SCond (c, t, e) ->
        SCond (subst_sfree_with_sbound id depth c,
               subst_sfree_with_sbound id depth t,
               subst_sfree_with_sbound id depth e)

let try_lambda s =
    let candidates = IntMap.bindings s.sym_map in
    List.map (fun (id, info) ->
        let new_sterm = subst_sfree_with_sbound id 0 s.sterm in
        let new_sym_map = IntMap.remove id s.sym_map in
        let param_t = info.sym_type in
        let body_t = s.styp in
        { s with
          sterm = SLambda (param_t, new_sterm);
          styp = TyClass (Prelude "Function", [param_t; body_t]);
          sym_map = new_sym_map }
    ) candidates

let try_invoke_k recv args =
    let all_proto_terms = recv :: args in
    let (all', sm, demands, neqs, nt, nsy, nfl, nml) = merge_proto_term_contexts all_proto_terms in
    let recv' = List.hd all' in
    let args' = List.tl all' in
    let result_tv = nt in
    let merged_view = {
        sterm = recv'.sterm; styp = recv'.styp; sym_map = sm;
        demands; label_neqs = neqs;
        next_tvar = nt; next_sym = nsy; next_fl = nfl; next_ml = nml
    } in
    let existing_mls = IntSet.elements (method_labels_in_proto_term merged_view) in
    let make_variant ml nml' nneqs =
        { sterm = SMethodInvoke (recv'.sterm, ml, List.map (fun a -> a.sterm) args');
          styp = TVar result_tv;
          sym_map = sm;
          demands = NeedMethod (recv'.styp, ml,
                                List.map (fun a -> a.styp) args',
                                TVar result_tv) :: demands;
          label_neqs = nneqs;
          next_tvar = result_tv + 1;
          next_sym = nsy;
          next_fl = nfl;
          next_ml = nml' }
    in
    let reuse_variants = List.map (fun ml ->
        make_variant ml nml neqs
    ) existing_mls in
    let fresh_ml = nml in
    let fresh_neqs = List.map (fun ml -> (LMethod, fresh_ml, ml)) existing_mls in
    let fresh_variant = make_variant fresh_ml (fresh_ml + 1) (fresh_neqs @ neqs) in
    reuse_variants @ [fresh_variant]

let try_cond cond then_ else_ =
    let (all', sm, demands, neqs, nt, nsy, nfl, nml) =
        merge_proto_term_contexts [cond; then_; else_] in
    let c' = List.nth all' 0 in
    let t' = List.nth all' 1 in
    let e' = List.nth all' 2 in
    let result_tv = nt in
    let result = TVar result_tv in
    let bool_ty = TyClass (Prelude "Boolean", []) in
    let new_demands =
        Subtype (c'.styp, bool_ty)
        :: Subtype (t'.styp, result)
        :: Subtype (e'.styp, result)
        :: demands in
    [{ sterm = SCond (c'.sterm, t'.sterm, e'.sterm);
       styp = result;
       sym_map = sm;
       demands = new_demands;
       label_neqs = neqs;
       next_tvar = result_tv + 1;
       next_sym = nsy;
       next_fl = nfl;
       next_ml = nml }]

let try_cond_dup s =
    let result_tv = s.next_tvar in
    let result = TVar result_tv in
    let bool_sterm = SNew (TyClass (Prelude "Boolean", []), []) in
    [{ s with
       sterm = SCond (bool_sterm, s.sterm, s.sterm);
       styp = result;
       demands = Subtype (s.styp, result) :: s.demands;
       next_tvar = result_tv + 1 }]

let try_array elems =
    let (elems', sm, demands, neqs, nt, nsy, nfl, nml) =
        merge_proto_term_contexts elems in
    let comp_tv = nt in
    let comp = TVar comp_tv in
    let elem_demands = List.map (fun e -> Subtype (e.styp, comp)) elems' in
    [{ sterm = SNew (TyArray comp, List.map (fun e -> e.sterm) elems');
       styp = TyArray comp;
       sym_map = sm;
       demands = elem_demands @ demands;
       label_neqs = neqs;
       next_tvar = comp_tv + 1;
       next_sym = nsy;
       next_fl = nfl;
       next_ml = nml }]

type method_entry = {
    mt_class : int;
    mt_label : method_label;
    mt_this_sym : int;
    mt_tparams : tparam_proto_term list;
    mt_params : (int * heph_type) list;
    mt_return : heph_type;
    mt_body : expr_proto_term;
}

type class_entry = {
    cl_label : int;
    cl_tparams : tparam_proto_term list;
    cl_parent : class_ref * heph_type list;
    cl_fields : (field_label * heph_type) list;
}

type program_proto_term = {
    classes : class_entry list;
    methods : method_entry list;
    main : expr_proto_term option;
    all_demands : demand list;
    all_label_neqs : label_neq list;
    tvar_scope : int IntMap.t;
    tvar_owner : int IntMap.t;
    tvar_method : int IntMap.t;
    next_class_label : int;
    next_tvar : int;
    next_fl : int;
    next_ml : int;
}

let class_decl_of p cl =
    List.find_opt (fun ce -> ce.cl_label = cl) p.classes

let scope_bounds p tv =
    match IntMap.find_opt tv p.tvar_owner with
    | None -> []
    | Some cl ->
        (match class_decl_of p cl with
         | Some ce -> List.map (fun tp -> tp.tp_bound) ce.cl_tparams
         | None -> [])

let rec tvars_of = function
    | TVar i -> IntSet.singleton i
    | t -> fold_type_children (fun a t -> IntSet.union a (tvars_of t)) IntSet.empty t

let method_of p ml = List.find_opt (fun me -> me.mt_label = ml) p.methods

let method_bounds p tv =
    match IntMap.find_opt tv p.tvar_method with
    | None -> []
    | Some ml ->
        (match method_of p ml with
         | Some me -> List.map (fun tp -> tp.tp_bound) me.mt_tparams
         | None -> [])

let parent_cref_of p = function
    | Prelude n -> prelude_parent n
    | Synth i ->
        (match class_decl_of p i with
         | Some ce -> Some (fst ce.cl_parent)
         | None -> None)

let rec subst_typaram args = function
    | TyParam i ->
        (try List.nth args i
         with Failure _ | Invalid_argument _ -> TyParam i)
    | t -> map_type_children (subst_typaram args) t

let parent_decl_of p = function
    | Prelude n ->
        (match prelude_parent n with
         | None -> None
         | Some par -> Some (par, []))
    | Synth i ->
        (match class_decl_of p i with
         | Some ce -> Some ce.cl_parent
         | None -> None)

let rec fields_of_class p cr args =
    match cr with
    | Prelude _ -> []
    | Synth i ->
        (match class_decl_of p i with
         | None -> []
         | Some ce ->
             let (parent_cr, parent_decl_args) = ce.cl_parent in
             let parent_args' = List.map (subst_typaram args) parent_decl_args in
             let parent_fields = fields_of_class p parent_cr parent_args' in
             let own_fields = List.map (fun (fl, ft) ->
                 (fl, subst_typaram args ft)) ce.cl_fields in
             parent_fields @ own_fields)

let fields_of_type p = function
    | TyClass (cr, args) -> fields_of_class p cr args
    | _ -> []

let rec type_equal a b =
    match a, b with
    | TyBot, TyBot -> true
    | TyClass (c1, a1), TyClass (c2, a2) ->
        class_ref_equal c1 c2 && List.length a1 = List.length a2 &&
        List.for_all2 type_equal a1 a2
    | TyParam i, TyParam j -> i = j
    | TVar i, TVar j -> i = j
    | Wild (v1, t1), Wild (v2, t2) -> v1 = v2 && type_equal t1 t2
    | MTParam i, MTParam j -> i = j
    | TyArray a, TyArray b -> type_equal a b
    | _ -> false

let rec is_subtype_cr p sub sup =
    if class_ref_equal sub sup then true
    else
        match parent_cref_of p sub with
        | None -> false
        | Some par -> is_subtype_cr p par sup

let tparam_variances_of p = function
    | Prelude n -> prelude_tparam_variances n
    | Synth i ->
        (match class_decl_of p i with
         | Some ce -> List.map (fun tp -> tp.tp_variance) ce.cl_tparams
         | None -> [])

let compose_variance outer inner =
    match outer, inner with
    | Invariant, _ -> Invariant
    | _, Invariant -> Invariant
    | Covariant, v -> v
    | Contravariant, Covariant -> Contravariant
    | Contravariant, Contravariant -> Covariant

let variance_allowed pos_v decl_v =
    match pos_v, decl_v with
    | Invariant, Invariant -> true
    | Invariant, _ -> false
    | Covariant, (Covariant | Invariant) -> true
    | Covariant, Contravariant -> false
    | Contravariant, (Contravariant | Invariant) -> true
    | Contravariant, Covariant -> false

let variance_check_type p tps pos ty =
    let rec walk pos = function
        | TyBot -> true
        | TVar _ -> true
        | TyParam i ->
            i >= 0 && i < List.length tps &&
            variance_allowed pos (List.nth tps i).tp_variance
        | TyClass (cr, args) ->
            let arg_vs = tparam_variances_of p cr in
            List.length args = List.length arg_vs &&
            List.for_all2 (fun a v_i ->
                walk (compose_variance pos v_i) a
            ) args arg_vs
        | Wild (wv, t) -> walk (compose_variance pos wv) t
        | MTParam _ | Hole _ -> true
        | TyArray t -> walk pos t
    in
    walk pos ty

let rec is_subtype ?(bounds=[]) ?(mbounds=[]) p sub sup =
    if type_equal sub sup then true
    else match sub, sup with
    | TyBot, _ -> true
    | _, TyBot -> false
    | TyClass (c1, a1), TyClass (c2, a2) ->
        if class_ref_equal c1 c2 then
            args_contained ~bounds ~mbounds p c1 a1 a2
        else
            (match parent_decl_of p c1 with
             | None -> false
             | Some (parent_cr, parent_decl_args) ->
                 let parent_args' = List.map (subst_typaram a1) parent_decl_args in
                 is_subtype ~bounds ~mbounds p (TyClass (parent_cr, parent_args')) sup)
    | TyParam i, TyParam j when i = j -> true
    | TyParam i, _ ->
        (match List.nth_opt bounds i with
         | Some b -> is_subtype ~bounds ~mbounds p b sup
         | None -> false)
    | TVar i, TVar j -> i = j
    | Wild (Covariant, b), _ -> is_subtype ~bounds ~mbounds p b sup
    | Wild (_, _), _ -> is_subtype ~bounds ~mbounds p (TyClass (Prelude "Object", [])) sup
    | MTParam i, MTParam j when i = j -> true
    | MTParam i, _ ->
        (match List.nth_opt mbounds i with
         | Some b -> is_subtype ~bounds ~mbounds p b sup
         | None -> false)
    | TyArray a, TyArray b -> is_subtype ~bounds ~mbounds p a b
    | _ -> false

and arg_contains ?(bounds=[]) ?(mbounds=[]) p v x y =
    let sub = is_subtype ~bounds ~mbounds p in
    match y with
    | Wild (Covariant, t) ->
        (match x with
         | Wild (Covariant, s) -> sub s t
         | Wild _ -> false
         | _ -> sub x t)
    | Wild (Contravariant, t) ->
        (match x with
         | Wild (Contravariant, s) -> sub t s
         | Wild _ -> false
         | _ -> sub t x)
    | Wild (Invariant, _) -> true
    | _ ->
        (match v with
         | Invariant -> type_equal x y
         | Covariant -> sub x y
         | Contravariant -> sub y x)

and args_contained ?(bounds=[]) ?(mbounds=[]) p cr a1 a2 =
    let vs = tparam_variances_of p cr in
    List.length a1 = List.length a2 && List.length a1 = List.length vs &&
    List.for_all2 (fun (x, y) v -> arg_contains ~bounds ~mbounds p v x y)
        (List.combine a1 a2) vs

let make_empty_program () =
    { classes = []; methods = []; main = None;
      all_demands = []; all_label_neqs = [];
      tvar_scope = IntMap.empty;
      tvar_owner = IntMap.empty;
      tvar_method = IntMap.empty;
      next_class_label = 0; next_tvar = 0;
      next_fl = 0; next_ml = 0 }

let tparam_count_options = [0; 1; 2]
let variance_options = [Invariant; Covariant; Contravariant]

let rec variance_tuples n =
    if n = 0 then [[]]
    else
        let rest = variance_tuples (n - 1) in
        List.concat_map (fun r ->
            List.map (fun v -> v :: r) variance_options
        ) rest

let tuple_cap = 16

let bounded_tuples ~cap cands k =
    let out = ref [] in
    let count = ref 0 in
    let rec emit prefix remaining =
        if !count >= cap then ()
        else if remaining = 0 then begin
            out := List.rev prefix :: !out;
            incr count
        end
        else
            List.iter (fun c ->
                if !count < cap then
                    emit (c :: prefix) (remaining - 1)
            ) cands
    in
    emit [] k;
    List.rev !out

let capped_tuples cands k =
    bounded_tuples ~cap:tuple_cap cands k

let parent_arg_candidates p ~own_tparam_count =
    let tparams = List.init own_tparam_count (fun i -> TyParam i) in
    let prelude_nongeneric = List.filter_map (fun pd ->
        if prelude_tparam_variances pd.pr_name = []
        then Some (TyClass (Prelude pd.pr_name, []))
        else None
    ) prelude in
    let synth_nongeneric = List.filter_map (fun ce ->
        if ce.cl_tparams = [] then Some (TyClass (Synth ce.cl_label, []))
        else None
    ) p.classes in
    let synth_object_inst = List.filter_map (fun ce ->
        let n = List.length ce.cl_tparams in
        if n = 0 then None
        else Some (TyClass (Synth ce.cl_label,
            List.init n (fun _ -> TyClass (Prelude "Object", []))))
    ) p.classes in
    tparams @ prelude_nongeneric @ synth_nongeneric @ synth_object_inst

let wildcard_field_candidates p =
    let number = TyClass (Prelude "Number", []) in
    List.concat_map (fun ce ->
        match ce.cl_tparams with
        | [{ tp_bound = TyClass (Prelude _, []) as b; _ }] ->
            let inner = if type_equal b (TyClass (Prelude "Object", []))
                        then number else b in
            [ TyClass (Synth ce.cl_label, [Wild (Covariant, inner)]);
              TyClass (Synth ce.cl_label, [Wild (Contravariant, inner)]) ]
        | _ -> []
    ) p.classes

let tvar_wildcard_field_candidates p ~own_tparams =
    let own_bounds = List.map (fun tp -> tp.tp_bound) own_tparams in
    let object_ty = TyClass (Prelude "Object", []) in
    List.concat_map (fun ce ->
        match ce.cl_tparams with
        | [{ tp_bound = b; _ }] ->
            List.concat (List.mapi (fun i _ ->
                let pi = TyParam i in
                (if is_subtype ~bounds:own_bounds p pi b
                 then [TyClass (Synth ce.cl_label, [Wild (Covariant, pi)])] else [])
                @ (if type_equal b object_ty
                   then [TyClass (Synth ce.cl_label, [Wild (Contravariant, pi)])]
                   else [])
            ) own_tparams)
        | _ -> []
    ) p.classes

let field_type_candidates ?(tvar_wild=false) p ~own_tparams =
    let n = List.length own_tparams in
    parent_arg_candidates p ~own_tparam_count:n @ wildcard_field_candidates p
    @ (if tvar_wild then tvar_wildcard_field_candidates p ~own_tparams else [])

let class_variants_cap = 32

let bound_candidates_for p ~preceding_count =
    let tparam_refs = List.init preceding_count (fun j -> TyParam j) in
    let prelude_nongeneric = List.filter_map (fun pd ->
        if prelude_tparam_variances pd.pr_name = []
        then Some (TyClass (Prelude pd.pr_name, []))
        else None
    ) prelude in
    let synth_nongeneric = List.filter_map (fun ce ->
        if ce.cl_tparams = [] then Some (TyClass (Synth ce.cl_label, []))
        else None
    ) p.classes in
    let synth_object_inst = List.filter_map (fun ce ->
        let n = List.length ce.cl_tparams in
        if n = 0 then None
        else Some (TyClass (Synth ce.cl_label,
            List.init n (fun _ -> TyClass (Prelude "Object", []))))
    ) p.classes in
    let synth_number_inst = List.filter_map (fun ce ->
        match ce.cl_tparams with
        | [{ tp_bound = TyClass (Prelude "Object", []); _ }] ->
            Some (TyClass (Synth ce.cl_label, [TyClass (Prelude "Number", [])]))
        | _ -> None
    ) p.classes in
    tparam_refs @ prelude_nongeneric @ synth_nongeneric
    @ synth_object_inst @ synth_number_inst

let tparam_proto_term_tuples p count =
    let rec go i =
        if i = count then [[]]
        else
            let bounds = bound_candidates_for p ~preceding_count:i in
            let rest = go (i + 1) in
            List.concat_map (fun b ->
                List.concat_map (fun v ->
                    List.map (fun r ->
                        { tp_variance = v; tp_bound = b } :: r
                    ) rest
                ) variance_options
            ) bounds
    in
    go 0

let bound_satisfied ?(bounds=[]) ?(mbounds=[]) p cr args =
    match cr with
    | Prelude _ -> true
    | Synth i ->
        (match class_decl_of p i with
         | None -> false
         | Some ce ->
             List.length args = List.length ce.cl_tparams &&
             List.for_all2 (fun arg tp ->
                 let bound' = subst_typaram args tp.tp_bound in
                 is_subtype ~bounds ~mbounds p arg bound'
             ) args ce.cl_tparams)

let try_add_class ?(max_identical = 0) ?(sample = false) p =
    let new_label = p.next_class_label in
    let identical_count ce =
        List.length (List.filter (fun c ->
            c.cl_tparams = ce.cl_tparams
            && c.cl_parent = ce.cl_parent
            && c.cl_fields = ce.cl_fields) p.classes) in
    let parent_options =
        List.map (fun n -> Prelude n) prelude_names
        @ List.map (fun ce -> Synth ce.cl_label) p.classes
    in
    let variants_seq = List.to_seq parent_options |> Seq.concat_map (fun pcr ->
        let par_tp_count = List.length (tparam_variances_of p pcr) in
        List.to_seq tparam_count_options |> Seq.concat_map (fun tp_count ->
            let tparam_tuples = tparam_proto_term_tuples p tp_count in
            List.to_seq tparam_tuples |> Seq.concat_map (fun own_tparams ->
                let par_arg_choices =
                    if par_tp_count = 0 then [[]]
                    else
                        let cands = parent_arg_candidates p
                            ~own_tparam_count:tp_count in
                        capped_tuples cands par_tp_count
                in
                let par_vs = tparam_variances_of p pcr in
                let own_bounds = List.map (fun tp -> tp.tp_bound) own_tparams in
                let legal_arg_choices = List.filter (fun args ->
                    List.length args = List.length par_vs &&
                    List.for_all2 (fun a v_i ->
                        variance_check_type p own_tparams v_i a
                    ) args par_vs
                    && bound_satisfied ~bounds:own_bounds p pcr args
                ) par_arg_choices in
                List.to_seq legal_arg_choices |> Seq.filter_map (fun par_args ->
                    let ce = {
                        cl_label = new_label;
                        cl_tparams = own_tparams;
                        cl_parent = (pcr, par_args);
                        cl_fields = [];
                    } in
                    if max_identical > 0 && identical_count ce >= max_identical
                    then None
                    else Some { p with classes = ce :: p.classes;
                                       next_class_label = new_label + 1 }))))
    in
    if not sample then variants_seq |> Seq.take class_variants_cap
    else
        let head = variants_seq |> Seq.take (class_variants_cap / 4) |> List.of_seq in
        let rng = Random.State.make [| Random.bits () |] in
        let pick l = List.nth l (Random.State.int rng (List.length l)) in
        let prelude_parents = Array.of_list (List.map (fun n -> Prelude n) prelude_names) in
        let synth_parents = Array.of_list (List.map (fun ce -> Synth ce.cl_label) p.classes) in
        let seen = ref (List.map (fun q -> List.hd q.classes) head) in
        let same a b = a.cl_tparams = b.cl_tparams && a.cl_parent = b.cl_parent in
        let rec draw acc attempts =
            if List.length acc >= class_variants_cap - List.length head
               || attempts = 0 then List.rev acc
            else
                let pcr =
                    if Array.length synth_parents > 0 && Random.State.bool rng
                    then synth_parents.(Random.State.int rng (Array.length synth_parents))
                    else prelude_parents.(Random.State.int rng (Array.length prelude_parents)) in
                let par_vs = tparam_variances_of p pcr in
                let tp_count = pick tparam_count_options in
                let object_ty = TyClass (Prelude "Object", []) in
                let own_tparams = List.fold_left (fun tps i ->
                    let bound = match Random.State.int rng 3 with
                        | 0 -> object_ty
                        | 1 when i > 0 -> TyParam (Random.State.int rng i)
                        | _ -> pick (bound_candidates_for p ~preceding_count:i) in
                    tps @ [{ tp_variance = pick variance_options; tp_bound = bound }]
                ) [] (List.init tp_count Fun.id) in
                let arg_cands = parent_arg_candidates p ~own_tparam_count:tp_count in
                let own_refs = List.init tp_count (fun i -> TyParam i) in
                let par_args = List.map (fun _ ->
                    if own_refs <> [] && Random.State.bool rng then pick own_refs
                    else pick arg_cands) par_vs in
                let own_bounds = List.map (fun tp -> tp.tp_bound) own_tparams in
                let ce = { cl_label = new_label; cl_tparams = own_tparams;
                           cl_parent = (pcr, par_args); cl_fields = [] } in
                let legal =
                    List.for_all2 (fun a v_i -> variance_check_type p own_tparams v_i a)
                        par_args par_vs
                    && bound_satisfied ~bounds:own_bounds p pcr par_args
                    && not (List.exists (same ce) !seen)
                    && not (max_identical > 0 && identical_count ce >= max_identical) in
                if legal then begin
                    seen := ce :: !seen;
                    draw ({ p with classes = ce :: p.classes;
                                   next_class_label = new_label + 1 } :: acc)
                        (attempts - 1)
                end else draw acc (attempts - 1)
        in
        List.to_seq (head @ draw [] (8 * class_variants_cap))

let rec bounds_satisfied_in_type ?(bounds=[]) p = function
    | TyClass (cr, args) ->
        List.for_all (bounds_satisfied_in_type ~bounds p) args
        && bound_satisfied ~bounds p cr args
    | t -> fold_type_children (fun ok t -> ok && bounds_satisfied_in_type ~bounds p t) true t

let try_add_field ?(tvar_wild=false) ?(scoped=false) p =
    if p.classes = [] then []
    else
        List.concat_map (fun target ->
            let cands = field_type_candidates ~tvar_wild p
                ~own_tparams:target.cl_tparams in
            let bounds = if scoped
                then List.map (fun tp -> tp.tp_bound) target.cl_tparams else [] in
            let legal = List.filter (fun ft ->
                variance_check_type p target.cl_tparams Invariant ft
                && bounds_satisfied_in_type ~bounds p ft
            ) cands in
            List.map (fun ft ->
                let fl = p.next_fl in
                let updated = { target with cl_fields = target.cl_fields @ [(fl, ft)] } in
                let classes' = List.map (fun ce ->
                    if ce.cl_label = target.cl_label then updated else ce
                ) p.classes in
                { p with classes = classes';
                         next_fl = fl + 1 }
            ) legal
        ) p.classes

let rec seq_product = function
    | [] -> Seq.return []
    | options :: rest ->
        let tail = seq_product rest in
        Seq.concat_map (fun x -> Seq.map (fun r -> x :: r) tail)
            (List.to_seq options)

let assign_cap = 50
let materialize_fl_cap = 20

let capped_label_mappings cap options_per_fl =
    seq_product (List.map (fun (efl, opts) ->
        List.map (fun pfl -> (efl, pfl)) opts) options_per_fl)
    |> Seq.take cap
    |> List.of_seq

let rec subst_fl_sterm old_fl new_fl = function
    | SFree _ | SBound _ | SNull _ as t -> t
    | SNew (ty, args) -> SNew (ty, List.map (subst_fl_sterm old_fl new_fl) args)
    | SFieldAccess (e, fl) ->
        SFieldAccess (subst_fl_sterm old_fl new_fl e,
                      if fl = old_fl then new_fl else fl)
    | SMethodInvoke (e, ml, args) ->
        SMethodInvoke (subst_fl_sterm old_fl new_fl e, ml,
                       List.map (subst_fl_sterm old_fl new_fl) args)
    | SLambda (ty, body) -> SLambda (ty, subst_fl_sterm old_fl new_fl body)
    | SCond (c, t, e) ->
        SCond (subst_fl_sterm old_fl new_fl c,
               subst_fl_sterm old_fl new_fl t,
               subst_fl_sterm old_fl new_fl e)

let subst_fl_demand old_fl new_fl = function
    | NeedField (r, fl, t) ->
        NeedField (r, (if fl = old_fl then new_fl else fl), t)
    | d -> d

let subst_fl_neq old_fl new_fl = function
    | (LField, l1, l2) ->
        (LField, (if l1 = old_fl then new_fl else l1),
                 (if l2 = old_fl then new_fl else l2))
    | n -> n

let subst_fl_proto_term old_fl new_fl s =
    { s with sterm = subst_fl_sterm old_fl new_fl s.sterm;
             demands = List.map (subst_fl_demand old_fl new_fl) s.demands;
             label_neqs = List.map (subst_fl_neq old_fl new_fl) s.label_neqs }

let try_assign_main p e =
    if p.main <> None then []
    else
        let e' = rename_proto_term p.next_tvar 0 0 0 e in
        let new_scope =
            let rec add acc i =
                if i >= e'.next_tvar then acc
                else add (IntMap.add i 0 acc) (i + 1)
            in add p.tvar_scope p.next_tvar in
        let expr_fls = IntSet.elements (field_labels_in_proto_term e') in
        let prog_fls = List.concat_map (fun ce ->
            List.map fst ce.cl_fields) p.classes in
        if expr_fls = [] then
            [{ p with main = Some e';
               all_demands = p.all_demands @ e'.demands;
               all_label_neqs = p.all_label_neqs @ e'.label_neqs;
               tvar_scope = new_scope;
               next_tvar = e'.next_tvar;
               next_fl = max p.next_fl e'.next_fl;
               next_ml = e'.next_ml }]
        else
            let options_per_fl = List.map (fun efl ->
                (efl, prog_fls @ [efl])
            ) expr_fls in
            let mappings = capped_label_mappings assign_cap options_per_fl in
            List.map (fun mapping ->
                let e'' = List.fold_left (fun acc (efl, pfl) ->
                    if efl = pfl then acc else subst_fl_proto_term efl pfl acc
                ) e' mapping in
                { p with main = Some e'';
                   all_demands = p.all_demands @ e''.demands;
                   all_label_neqs = p.all_label_neqs @ e''.label_neqs;
                   tvar_scope = new_scope;
                   next_tvar = e''.next_tvar;
                   next_fl = max p.next_fl e''.next_fl;
                   next_ml = e''.next_ml }
            ) mappings

let method_tparam_options ~generic next_tvar =
    if not generic then [([], next_tvar)]
    else
        let object_ty = TyClass (Prelude "Object", []) in
        [ ([], next_tvar);
          ([{ tp_variance = Invariant; tp_bound = object_ty }], next_tvar);
          ([{ tp_variance = Invariant; tp_bound = TVar next_tvar }], next_tvar + 1) ]

let try_materialize_method ?(rich = false) ?(generic = false) p e =
    if p.classes = [] then []
    else
    let e' = rename_proto_term p.next_tvar 0 0 0 e in
    let syms = IntMap.bindings e'.sym_map in
    List.concat_map (fun target_ce ->
        let n_tp = List.length target_ce.cl_tparams in
        let this_type =
            TyClass (Synth target_ce.cl_label,
                     List.init n_tp (fun i -> TyParam i)) in
        let build ~this_sym ~e_body ~params ~skip =
            let params_ok = List.for_all (fun (_, info) ->
                variance_check_type p target_ce.cl_tparams Contravariant info.sym_type
            ) params in
            let ret_ok = variance_check_type p target_ce.cl_tparams
                Covariant e_body.styp in
            if not (params_ok && ret_ok) then []
            else
            let ml = p.next_ml in
            let expr_fls = IntSet.elements (field_labels_in_proto_term e_body) in
            let prog_fls = List.concat_map (fun ce ->
                List.map fst ce.cl_fields) p.classes in
            let fl_options = List.map (fun efl -> (efl, prog_fls @ [efl])) expr_fls in
            let fl_mappings = capped_label_mappings materialize_fl_cap fl_options in
            let sig_has_tvar =
                List.exists (fun (_, info) -> not (IntSet.is_empty (tvars_of info.sym_type)))
                    params
                || not (IntSet.is_empty (tvars_of e_body.styp)) in
            let tparam_options =
                method_tparam_options ~generic:(generic && sig_has_tvar) e_body.next_tvar in
            List.concat_map (fun fl_map ->
                let e'' = List.fold_left (fun acc (efl, pfl) ->
                    if efl = pfl then acc else subst_fl_proto_term efl pfl acc
                ) e_body fl_map in
                List.map (fun (tparams, next_tvar) ->
                let me = {
                    mt_class = target_ce.cl_label;
                    mt_label = ml;
                    mt_this_sym = this_sym;
                    mt_tparams = tparams;
                    mt_params = List.map (fun (id, info) -> (id, info.sym_type)) params;
                    mt_return = e''.styp;
                    mt_body = e'';
                } in
                let add_range f acc =
                    let rec add acc i =
                        if i >= next_tvar then acc
                        else if Some i = skip then add acc (i + 1)
                        else add (f acc i) (i + 1)
                    in add acc p.next_tvar in
                let new_scope = add_range (fun acc i -> IntMap.add i n_tp acc) p.tvar_scope in
                let new_owner =
                    add_range (fun acc i -> IntMap.add i target_ce.cl_label acc) p.tvar_owner in
                let new_method =
                    if tparams = [] then p.tvar_method
                    else
                        let rec add acc i =
                            if i >= e''.next_tvar then acc
                            else if Some i = skip then add acc (i + 1)
                            else add (IntMap.add i ml acc) (i + 1)
                        in add p.tvar_method p.next_tvar in
                { p with
                  methods = me :: p.methods;
                  tvar_owner = new_owner;
                  tvar_method = new_method;
                  all_demands = p.all_demands @ e''.demands;
                  all_label_neqs = p.all_label_neqs @ e''.label_neqs;
                  tvar_scope = new_scope;
                  next_tvar = next_tvar;
                  next_ml = ml + 1;
                  next_fl = max p.next_fl e''.next_fl }
                ) tparam_options
            ) fl_mappings in
        let fresh_variant =
            match e'.sterm with
            | SFree _ ->
                build ~this_sym:e'.next_sym ~e_body:e'
                    ~params:(IntMap.bindings e'.sym_map) ~skip:None
            | _ when generic || (rich && not (IntMap.is_empty e'.sym_map)) ->
                build ~this_sym:e'.next_sym ~e_body:e'
                    ~params:(IntMap.bindings e'.sym_map) ~skip:None
            | _ -> [] in
        let pinned_variants =
            List.concat_map (fun (this_sym, this_info) ->
                match this_info.sym_type with
                | TVar this_tv ->
                    let e_pinned =
                        subst_tvar_with_type_in_proto_term this_tv this_type e' in
                    let params = List.filter (fun (id, _) -> id <> this_sym)
                        (IntMap.bindings e_pinned.sym_map) in
                    build ~this_sym ~e_body:e_pinned ~params ~skip:(Some this_tv)
                | _ -> []
            ) syms in
        fresh_variant @ pinned_variants
    ) p.classes

let rec tvars_in_type = function
    | TVar i -> IntSet.singleton i
    | t -> fold_type_children (fun a t -> IntSet.union a (tvars_in_type t)) IntSet.empty t

let rec tvars_in_sterm = function
    | SFree _ | SBound _ -> IntSet.empty
    | SNull t -> tvars_in_type t
    | SNew (t, args) ->
        List.fold_left (fun a s -> IntSet.union a (tvars_in_sterm s))
            (tvars_in_type t) args
    | SFieldAccess (e, _) -> tvars_in_sterm e
    | SMethodInvoke (e, _, args) ->
        List.fold_left (fun a s -> IntSet.union a (tvars_in_sterm s))
            (tvars_in_sterm e) args
    | SLambda (t, body) -> IntSet.union (tvars_in_type t) (tvars_in_sterm body)
    | SCond (c, t, e) ->
        IntSet.union (tvars_in_sterm c)
            (IntSet.union (tvars_in_sterm t) (tvars_in_sterm e))

let tvars_in_demand = function
    | NeedField (r, _, t) -> IntSet.union (tvars_in_type r) (tvars_in_type t)
    | NeedMethod (r, _, ps, t) ->
        List.fold_left (fun a p -> IntSet.union a (tvars_in_type p))
            (IntSet.union (tvars_in_type r) (tvars_in_type t)) ps
    | Subtype (a, b) -> IntSet.union (tvars_in_type a) (tvars_in_type b)
    | FieldCount (t, _) -> tvars_in_type t
    | TparamBound (_, _, b) -> tvars_in_type b

let tvars_in_expr e =
    let from_sterm = tvars_in_sterm e.sterm in
    let from_styp = tvars_in_type e.styp in
    let from_sym = IntMap.fold (fun _ info a ->
        IntSet.union a (tvars_in_type info.sym_type)
    ) e.sym_map IntSet.empty in
    let from_demands = List.fold_left (fun a d ->
        IntSet.union a (tvars_in_demand d)
    ) IntSet.empty e.demands in
    IntSet.union from_sterm
        (IntSet.union from_styp
            (IntSet.union from_sym from_demands))

let tvars_in_program p =
    let from_classes = List.fold_left (fun acc ce ->
        List.fold_left (fun a (_, ft) ->
            IntSet.union a (tvars_in_type ft)
        ) acc ce.cl_fields
    ) IntSet.empty p.classes in
    let from_main = match p.main with
        | None -> IntSet.empty
        | Some e -> tvars_in_expr e in
    let from_methods = List.fold_left (fun acc me ->
        let body = tvars_in_expr me.mt_body in
        let ret = tvars_in_type me.mt_return in
        let params = List.fold_left (fun a (_, t) ->
            IntSet.union a (tvars_in_type t)) IntSet.empty me.mt_params in
        let tbounds = List.fold_left (fun a tp ->
            IntSet.union a (tvars_in_type tp.tp_bound)) IntSet.empty me.mt_tparams in
        IntSet.union acc (IntSet.union body (IntSet.union ret (IntSet.union params tbounds)))
    ) IntSet.empty p.methods in
    let from_demands = List.fold_left (fun a d ->
        IntSet.union a (tvars_in_demand d)
    ) IntSet.empty p.all_demands in
    IntSet.union from_classes
        (IntSet.union from_main
            (IntSet.union from_methods from_demands))

type fault =
    | BreakDemand of (int * heph_type) list
    | MutateVar
    | MutateBVar
    | AddBoundViolation of class_entry
    | BadDefault
    | MutateReturn of method_label

type tagged_proto_term =
    | ExprProtoTerm of expr_proto_term
    | ProgramProtoTerm of program_proto_term
    | FaultedProgram of program_proto_term * fault

type prototerm = tagged_proto_term
type fact = tagged_fact

let prototerm_tvar_count = function
    | ExprProtoTerm e -> IntSet.cardinal (tvars_in_expr e)
    | ProgramProtoTerm p | FaultedProgram (p, _) -> IntSet.cardinal (tvars_in_program p)

let sort_program = 0
let sort_expr = 1

let sort_count = 2
let string_of_sort = function
    | 0 -> "program"
    | 1 -> "expr"
    | _ -> "?"

let prototerm_sort = function
    | ExprProtoTerm _ -> sort_expr
    | ProgramProtoTerm _ | FaultedProgram _ -> sort_program

let output_sorts = [sort_program]

type prototerm_key =
    | EK of proto_term * heph_type * demand list * label_neq list
    | PK of class_entry list * method_entry list * expr_proto_term option
    | FK of class_entry list * method_entry list * expr_proto_term option * fault
type fact_key = string

let prototerm_key = function
    | ExprProtoTerm s -> EK (s.sterm, s.styp, s.demands, s.label_neqs)
    | ProgramProtoTerm p -> PK (p.classes, p.methods, p.main)
    | FaultedProgram (p, f) -> FK (p.classes, p.methods, p.main, f)
let fact_key (f : tagged_fact) = f.tf_rendered

let compare_prototerm_key = compare
let compare_fact_key = compare

let rec sterm_nodes_hp = function
    | SFree _ | SBound _ | SNull _ -> 1
    | SNew (_, args) ->
        1 + List.fold_left (fun acc a -> acc + sterm_nodes_hp a) 0 args
    | SFieldAccess (e, _) | SLambda (_, e) -> 1 + sterm_nodes_hp e
    | SMethodInvoke (e, _, args) ->
        1 + sterm_nodes_hp e
          + List.fold_left (fun acc a -> acc + sterm_nodes_hp a) 0 args
    | SCond (c, t, e) ->
        1 + sterm_nodes_hp c + sterm_nodes_hp t + sterm_nodes_hp e

let prototerm_min_size = function
    | ExprProtoTerm s -> sterm_nodes_hp s.sterm
    | ProgramProtoTerm p | FaultedProgram (p, _) ->
        (match p.main with
         | Some e -> sterm_nodes_hp e.sterm
         | None -> 1)

let string_of_prototerm sk = match sk with
    | ExprProtoTerm s ->
        let base = string_of_sterm s.sterm ^ " : " ^ string_of_type s.styp in
        let n = List.length s.demands in
        if IntMap.is_empty s.sym_map && n = 0 then base
        else
            let ctx = if IntMap.is_empty s.sym_map then "" else
                let syms = IntMap.bindings s.sym_map in
                "  {" ^ String.concat ", " (List.map (fun (id, info) ->
                    "x" ^ string_of_int id ^ ": " ^ string_of_type info.sym_type
                ) syms) ^ "}" in
            let d = if n = 0 then "" else "  (" ^ string_of_int n ^ " demands)" in
            base ^ ctx ^ d
    | ProgramProtoTerm p | FaultedProgram (p, _) ->
        let nc = List.length p.classes in
        let nf = List.fold_left (fun acc ce -> acc + List.length ce.cl_fields) 0 p.classes in
        let nm = List.length p.methods in
        let main_s = if p.main = None then ", no main" else ", with main" in
        let fault_s = match sk with FaultedProgram _ -> ", faulted" | _ -> "" in
        Printf.sprintf "program(%d classes, %d fields, %d methods%s%s)" nc nf nm main_s fault_s
