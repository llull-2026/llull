open HephPrograms

type config = {
    auto_close     : bool;
    max_tvars      : int;
    max_type_depth : int;
    assignment_cap : int;
    max_identical_classes : int;
}

type proto_term =
    | SFree of int
    | SBound of int
    | SNew of heph_type * proto_term list
    | SFieldAccess of proto_term * field_label
    | SMethodInvoke of proto_term * method_label * proto_term list
    | SLambda of heph_type * proto_term
    | SIf of heph_type * proto_term * proto_term * proto_term

let rec string_of_sterm = function
    | SFree id -> "x" ^ string_of_int id
    | SBound i -> "#" ^ string_of_int i
    | SNew (ty, []) -> "new " ^ string_of_type ty ^ "()"
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
    | SIf (_, c, t, e) ->
        "if (" ^ string_of_sterm c ^ ") " ^ string_of_sterm t ^
        " else " ^ string_of_sterm e

and string_of_sterm_recv t =
    match t with
    | SNew _ | SLambda _ | SIf _ -> "(" ^ string_of_sterm t ^ ")"
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
    | SFree _ | SBound _ -> IntSet.empty
    | SNew (_, args) ->
        List.fold_left (fun acc a -> IntSet.union acc (field_labels_in_sterm a))
            IntSet.empty args
    | SFieldAccess (e, fl) -> IntSet.add fl (field_labels_in_sterm e)
    | SMethodInvoke (e, _, args) ->
        List.fold_left (fun acc a -> IntSet.union acc (field_labels_in_sterm a))
            (field_labels_in_sterm e) args
    | SLambda (_, body) -> field_labels_in_sterm body
    | SIf (_, c, t, e) ->
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
    | TyClass (cr, args) -> TyClass (cr, List.map (rename_type off_tv) args)
    | TyParam _ as t -> t
    | TyBot -> TyBot

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
    | SIf (ty, c, t, e) ->
        SIf (rename_type off_tv ty,
             rename_sterm off_tv off_sym off_fl off_ml c,
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
    | SNew (ty, args) -> SNew (ty, List.map (subst_sfree j i) args)
    | SFieldAccess (e, fl) -> SFieldAccess (subst_sfree j i e, fl)
    | SMethodInvoke (e, ml, args) ->
        SMethodInvoke (subst_sfree j i e, ml, List.map (subst_sfree j i) args)
    | SLambda (ty, body) -> SLambda (ty, subst_sfree j i body)
    | SIf (ty, c, t, e) ->
        SIf (ty, subst_sfree j i c, subst_sfree j i t, subst_sfree j i e)

let rec subst_tvar_type old_id new_id = function
    | TVar i when i = old_id -> TVar new_id
    | TVar _ as t -> t
    | TyClass (cr, args) -> TyClass (cr, List.map (subst_tvar_type old_id new_id) args)
    | TyParam _ | TyBot as t -> t

let rec subst_tvar_sterm old_id new_id = function
    | SFree _ | SBound _ as t -> t
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
    | SIf (ty, c, t, e) ->
        SIf (subst_tvar_type old_id new_id ty,
             subst_tvar_sterm old_id new_id c,
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
    | TVar _ as t -> t
    | TyClass (cr, args) ->
        TyClass (cr, List.map (subst_tvar_with_type_in_type old_id repl) args)
    | TyParam _ | TyBot as t -> t

let rec subst_tvar_with_type_in_sterm old_id repl = function
    | SFree _ | SBound _ as t -> t
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
    | SIf (ty, c, t, e) ->
        SIf (subst_tvar_with_type_in_type old_id repl ty,
             subst_tvar_with_type_in_sterm old_id repl c,
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
    | SFree _ | SBound _ -> IntSet.empty
    | SNew (_, args) ->
        List.fold_left (fun acc a -> IntSet.union acc (method_labels_in_sterm a))
            IntSet.empty args
    | SFieldAccess (e, _) -> method_labels_in_sterm e
    | SIf (_, c, t, e) ->
        IntSet.union (method_labels_in_sterm c)
            (IntSet.union (method_labels_in_sterm t) (method_labels_in_sterm e))
    | SMethodInvoke (e, ml, args) ->
        List.fold_left (fun acc a -> IntSet.union acc (method_labels_in_sterm a))
            (IntSet.add ml (method_labels_in_sterm e)) args
    | SLambda (_, body) -> method_labels_in_sterm body

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
    | SNew (ty, args) ->
        SNew (ty, List.map (subst_sfree_with_sbound id depth) args)
    | SFieldAccess (e, fl) ->
        SFieldAccess (subst_sfree_with_sbound id depth e, fl)
    | SMethodInvoke (e, ml, args) ->
        SMethodInvoke (subst_sfree_with_sbound id depth e, ml,
                       List.map (subst_sfree_with_sbound id depth) args)
    | SLambda (ty, body) ->
        SLambda (ty, subst_sfree_with_sbound id (depth + 1) body)
    | SIf (ty, c, t, e) ->
        SIf (ty, subst_sfree_with_sbound id depth c,
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

let try_if cond then_ else_ =
    let (all', sm, demands, neqs, nt, nsy, nfl, nml) =
        merge_proto_term_contexts [cond; then_; else_] in
    match all' with
    | [c'; t'; e'] ->
        let result_tv = nt in
        let result = TVar result_tv in
        let boolean = TyClass (Prelude "Boolean", []) in
        [{ sterm = SIf (result, c'.sterm, t'.sterm, e'.sterm);
           styp = result;
           sym_map = sm;
           demands = Subtype (c'.styp, boolean)
                     :: Subtype (t'.styp, result)
                     :: Subtype (e'.styp, result)
                     :: demands;
           label_neqs = neqs;
           next_tvar = result_tv + 1;
           next_sym = nsy;
           next_fl = nfl;
           next_ml = nml }]
    | _ -> []

type method_entry = {
    mt_class : int;
    mt_label : method_label;
    mt_this_sym : int;
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
    next_class_label : int;
    next_tvar : int;
    next_fl : int;
    next_ml : int;
}

let class_decl_of p cl =
    List.find_opt (fun ce -> ce.cl_label = cl) p.classes

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
    | TyClass (cr, ts) -> TyClass (cr, List.map (subst_typaram args) ts)
    | TVar _ as t -> t
    | TyBot -> TyBot

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
    in
    walk pos ty

let rec is_subtype p sub sup =
    if type_equal sub sup then true
    else match sub, sup with
    | TyBot, _ -> true
    | _, TyBot -> false
    | TyClass (c1, a1), TyClass (c2, a2) ->
        if class_ref_equal c1 c2 then
            args_contained p c1 a1 a2
        else
            (match parent_decl_of p c1 with
             | None -> false
             | Some (parent_cr, parent_decl_args) ->
                 let parent_args' = List.map (subst_typaram a1) parent_decl_args in
                 is_subtype p (TyClass (parent_cr, parent_args')) sup)
    | TyParam i, TyParam j -> i = j
    | TVar i, TVar j -> i = j
    | _ -> false

and args_contained p cr a1 a2 =
    let vs = tparam_variances_of p cr in
    List.length a1 = List.length a2 && List.length a1 = List.length vs &&
    List.for_all2 (fun (x, y) v ->
        match v with
        | Invariant -> type_equal x y
        | Covariant -> is_subtype p x y
        | Contravariant -> is_subtype p y x
    ) (List.combine a1 a2) vs

let make_empty_program () =
    { classes = []; methods = []; main = None;
      all_demands = []; all_label_neqs = [];
      tvar_scope = IntMap.empty;
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

let field_type_candidates p ~own_tparams =
    let n = List.length own_tparams in
    parent_arg_candidates p ~own_tparam_count:n

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
    tparam_refs @ prelude_nongeneric @ synth_nongeneric @ synth_object_inst

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

let bound_satisfied p cr args =
    match cr with
    | Prelude _ -> true
    | Synth i ->
        (match class_decl_of p i with
         | None -> false
         | Some ce ->
             List.length args = List.length ce.cl_tparams &&
             List.for_all2 (fun arg tp ->
                 let bound' = subst_typaram args tp.tp_bound in
                 is_subtype p arg bound'
             ) args ce.cl_tparams)

let try_add_class ?(max_identical = 0) p =
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
                let legal_arg_choices = List.filter (fun args ->
                    List.length args = List.length par_vs &&
                    List.for_all2 (fun a v_i ->
                        variance_check_type p own_tparams v_i a
                    ) args par_vs
                    && bound_satisfied p pcr args
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
    variants_seq |> Seq.take class_variants_cap

let rec bounds_satisfied_in_type p = function
    | TyBot | TVar _ | TyParam _ -> true
    | TyClass (cr, args) ->
        List.for_all (bounds_satisfied_in_type p) args
        && bound_satisfied p cr args

let try_add_field p =
    if p.classes = [] then []
    else
        List.concat_map (fun target ->
            let cands = field_type_candidates p ~own_tparams:target.cl_tparams in
            let legal = List.filter (fun ft ->
                variance_check_type p target.cl_tparams Invariant ft
                && bounds_satisfied_in_type p ft
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
    | SFree _ | SBound _ as t -> t
    | SNew (ty, args) -> SNew (ty, List.map (subst_fl_sterm old_fl new_fl) args)
    | SFieldAccess (e, fl) ->
        SFieldAccess (subst_fl_sterm old_fl new_fl e,
                      if fl = old_fl then new_fl else fl)
    | SMethodInvoke (e, ml, args) ->
        SMethodInvoke (subst_fl_sterm old_fl new_fl e, ml,
                       List.map (subst_fl_sterm old_fl new_fl) args)
    | SLambda (ty, body) -> SLambda (ty, subst_fl_sterm old_fl new_fl body)
    | SIf (ty, c, t, e) ->
        SIf (ty, subst_fl_sterm old_fl new_fl c,
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

let try_materialize_method p e =
    if p.classes = [] then []
    else
    let n_syms = IntMap.cardinal e.sym_map in
    if n_syms = 0 then []
    else
    let e' = rename_proto_term p.next_tvar 0 0 0 e in
    let syms = IntMap.bindings e'.sym_map in
    List.concat_map (fun target_ce ->
        let n_tp = List.length target_ce.cl_tparams in
        let this_type =
            TyClass (Synth target_ce.cl_label,
                     List.init n_tp (fun i -> TyParam i)) in
        List.concat_map (fun (this_sym, this_info) ->
            match this_info.sym_type with
            | TVar this_tv ->
                let e_pinned = subst_tvar_with_type_in_proto_term this_tv this_type e' in
                let params = List.filter (fun (id, _) -> id <> this_sym)
                    (IntMap.bindings e_pinned.sym_map) in
                let params_ok = List.for_all (fun (_, info) ->
                    variance_check_type p target_ce.cl_tparams Contravariant info.sym_type
                ) params in
                let ret_ok = variance_check_type p target_ce.cl_tparams
                    Covariant e_pinned.styp in
                if not (params_ok && ret_ok) then []
                else
                let ml = p.next_ml in
                let expr_fls = IntSet.elements (field_labels_in_proto_term e_pinned) in
                let prog_fls = List.concat_map (fun ce ->
                    List.map fst ce.cl_fields) p.classes in
                let fl_options = List.map (fun efl ->
                    (efl, prog_fls @ [efl])
                ) expr_fls in
                let fl_mappings = capped_label_mappings materialize_fl_cap fl_options in
                List.map (fun fl_map ->
                    let e'' = List.fold_left (fun acc (efl, pfl) ->
                        if efl = pfl then acc else subst_fl_proto_term efl pfl acc
                    ) e_pinned fl_map in
                    let me = {
                        mt_class = target_ce.cl_label;
                        mt_label = ml;
                        mt_this_sym = this_sym;
                        mt_params = List.map (fun (id, info) -> (id, info.sym_type)) params;
                        mt_return = e''.styp;
                        mt_body = e'';
                    } in
                    let new_scope =
                        let rec add acc i =
                            if i >= e'.next_tvar then acc
                            else if i = this_tv then add acc (i + 1)
                            else add (IntMap.add i n_tp acc) (i + 1)
                        in add p.tvar_scope p.next_tvar in
                    { p with
                      methods = me :: p.methods;
                      all_demands = p.all_demands @ e''.demands;
                      all_label_neqs = p.all_label_neqs @ e''.label_neqs;
                      tvar_scope = new_scope;
                      next_tvar = e''.next_tvar;
                      next_ml = ml + 1;
                      next_fl = max p.next_fl e''.next_fl }
                ) fl_mappings
            | _ -> []
        ) syms
    ) p.classes

let rec tvars_in_type = function
    | TVar i -> IntSet.singleton i
    | TyClass (_, args) ->
        List.fold_left (fun a t -> IntSet.union a (tvars_in_type t)) IntSet.empty args
    | TyParam _ | TyBot -> IntSet.empty

let rec tvars_in_sterm = function
    | SFree _ | SBound _ -> IntSet.empty
    | SNew (t, args) ->
        List.fold_left (fun a s -> IntSet.union a (tvars_in_sterm s))
            (tvars_in_type t) args
    | SFieldAccess (e, _) -> tvars_in_sterm e
    | SMethodInvoke (e, _, args) ->
        List.fold_left (fun a s -> IntSet.union a (tvars_in_sterm s))
            (tvars_in_sterm e) args
    | SLambda (t, body) -> IntSet.union (tvars_in_type t) (tvars_in_sterm body)
    | SIf (ty, c, t, e) ->
        IntSet.union (tvars_in_type ty)
            (IntSet.union (tvars_in_sterm c)
                (IntSet.union (tvars_in_sterm t) (tvars_in_sterm e)))

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
        IntSet.union acc (IntSet.union body (IntSet.union ret params))
    ) IntSet.empty p.methods in
    let from_demands = List.fold_left (fun a d ->
        IntSet.union a (tvars_in_demand d)
    ) IntSet.empty p.all_demands in
    IntSet.union from_classes
        (IntSet.union from_main
            (IntSet.union from_methods from_demands))

type fault =
    | BreakDemand of (int * heph_type) list
    | MutateMain
    | AddBoundViolation of class_entry

type tagged_proto_term =
    | ExprProtoTerm of expr_proto_term
    | ProgramProtoTerm of program_proto_term
    | FaultedProgram of program_proto_term * fault

type prototerm = tagged_proto_term
type fact = tagged_fact

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
let fact_key (f : tagged_fact) = Digest.string f.tf_rendered

let compare_prototerm_key = compare
let compare_fact_key = compare

let rec sterm_nodes_hp = function
    | SFree _ | SBound _ -> 1
    | SNew (_, args) ->
        1 + List.fold_left (fun acc a -> acc + sterm_nodes_hp a) 0 args
    | SFieldAccess (e, _) | SLambda (_, e) -> 1 + sterm_nodes_hp e
    | SMethodInvoke (e, _, args) ->
        1 + sterm_nodes_hp e
          + List.fold_left (fun acc a -> acc + sterm_nodes_hp a) 0 args
    | SIf (_, c, t, e) ->
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
