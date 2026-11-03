open HephRwPrograms
open HephRwPrototerms

let shuffle lst =
    let a = Array.of_list lst in
    for i = Array.length a - 1 downto 1 do
        let j = Random.int (i + 1) in
        let t = a.(i) in a.(i) <- a.(j); a.(j) <- t
    done;
    Array.to_list a

let diag_product (dims : 'a array list) : 'a list Seq.t =
    let dims = Array.of_list dims in
    let n = Array.length dims in
    if Array.exists (fun a -> Array.length a = 0) dims then Seq.empty
    else
        let maxs = Array.map (fun a -> Array.length a - 1) dims in
        let suf = Array.make (n + 1) 0 in
        for k = n - 1 downto 0 do suf.(k) <- suf.(k + 1) + maxs.(k) done;
        let rec comps k s =
            if k = n then (if s = 0 then Seq.return [] else Seq.empty)
            else
                let lo = max 0 (s - suf.(k + 1)) and hi = min s maxs.(k) in
                Seq.concat_map (fun i ->
                    Seq.map (fun rest -> dims.(k).(i) :: rest) (comps (k + 1) (s - i)))
                    (Seq.init (max 0 (hi - lo + 1)) (fun d -> lo + d)) in
        Seq.concat_map (comps 0) (Seq.init (suf.(0) + 1) Fun.id)

let all_tuples cands k =
    List.of_seq (diag_product (List.init k (fun _ -> Array.of_list cands)))

let types_up_to ?(bounds=[]) ?(mtparams=0) ?(randomize=false) ?(multi_wild=false)
        ?(cap=tuple_cap) ?(all=false)
        p ~scope_tparams depth =
    let object_ty = TyClass (Prelude "Object", []) in
    let mbounds = List.init mtparams (fun _ -> object_ty) in
    let tparams = List.init scope_tparams (fun i -> TyParam i) in
    let mtps = List.init mtparams (fun i -> MTParam i) in
    let prelude_nongeneric = List.filter_map (fun pd ->
        if prelude_tparam_variances pd.pr_name = []
        then Some (TyClass (Prelude pd.pr_name, []))
        else None
    ) prelude in
    let synth_nongeneric = List.filter_map (fun ce ->
        if ce.cl_tparams = [] then Some (TyClass (Synth ce.cl_label, []))
        else None
    ) p.classes in
    let depth0 = prelude_nongeneric @ tparams @ mtps @ synth_nongeneric in
    let wilds = List.concat_map (fun t ->
        [Wild (Covariant, t); Wild (Contravariant, t)]) depth0 in
    let ok cr args = bound_satisfied ~bounds ~mbounds p cr args in
    let bounded_tuples ~cap l n = if all then all_tuples l n else bounded_tuples ~cap l n in
    let rec up_to d =
        Generator.check_term_deadline ();
        if d = 0 then depth0
        else
            let lower = up_to (d - 1) in
            let arg_pool n =
                if n >= 2 && multi_wild then
                    let l = lower @ wilds in if randomize then shuffle l else l
                else if randomize then shuffle lower else lower in
            let prelude_generic_instances = List.concat_map (fun pd ->
                let n = List.length (prelude_tparam_variances pd.pr_name) in
                if n = 0 then []
                else
                    let arg_tuples = bounded_tuples ~cap (arg_pool n) n in
                    List.map (fun args -> TyClass (Prelude pd.pr_name, args))
                        arg_tuples
            ) prelude in
            let synth_generic_instances = List.concat_map (fun ce ->
                let n = List.length ce.cl_tparams in
                if n = 0 then []
                else
                    let arg_tuples = bounded_tuples ~cap (arg_pool n) n in
                    List.filter_map (fun args ->
                        if ok (Synth ce.cl_label) args
                        then Some (TyClass (Synth ce.cl_label, args))
                        else None
                    ) arg_tuples
            ) p.classes in
            let single_generic =
                List.filter_map (fun ce ->
                    match ce.cl_tparams with
                    | [tp] -> Some (Synth ce.cl_label, tp.tp_bound)
                    | _ -> None
                ) p.classes
                @ List.filter_map (fun pd ->
                    match prelude_tparam_variances pd.pr_name with
                    | [_] -> Some (Prelude pd.pr_name, object_ty)
                    | _ -> None
                ) prelude in
            let wildcard_instances =
                List.concat_map (fun (cr, bound) ->
                    List.concat_map (fun inner ->
                        (if is_subtype ~bounds ~mbounds p inner bound
                         then [TyClass (cr, [Wild (Covariant, inner)])] else [])
                        @ (if type_equal bound object_ty
                           then [TyClass (cr, [Wild (Contravariant, inner)])] else [])
                    ) depth0
                ) single_generic in
            lower @ prelude_generic_instances @ synth_generic_instances
            @ wildcard_instances
    in
    up_to depth

let rec resolve_type assignment = function
    | TVar i ->
        (match List.assoc_opt i assignment with
         | Some t -> t
         | None -> TyClass (Prelude "Object", []))
    | t -> map_type_children (resolve_type assignment) t

let ivar j = TVar (-1 - j)

let rec mtparams_to_ivars = function
    | MTParam j -> ivar j
    | t -> map_type_children mtparams_to_ivars t

let rec subst_ivars sigma = function
    | TVar k when k < 0 ->
        (match List.assoc_opt (-1 - k) sigma with Some t -> t | None -> TVar k)
    | t -> map_type_children (subst_ivars sigma) t

let rec collect_ivars formal actual acc =
    match formal, actual with
    | TVar k, _ when k < 0 -> (-1 - k, actual) :: acc
    | TyClass (_, fa), TyClass (_, aa) when List.length fa = List.length aa ->
        List.fold_left2 (fun acc f a -> collect_ivars f a acc) acc fa aa
    | Wild (_, f), Wild (_, a) | TyArray f, TyArray a -> collect_ivars f a acc
    | _ -> acc

let rec lookup_method_on ?(resolve = Fun.id) p methods cr args ml =
    match cr with
    | Prelude n ->
        (match prelude_method_signature n ml with
         | Some (params, ret) ->
             Some ([], List.map (subst_typaram args) params,
                   subst_typaram args ret)
         | None ->
             match prelude_parent n with
             | None -> None
             | Some par -> lookup_method_on ~resolve p methods par [] ml)
    | Synth i ->
        (match List.find_opt (fun me ->
            me.mt_class = i && me.mt_label = ml) methods with
         | Some me ->
             let view t = subst_typaram args (mtparams_to_ivars (resolve t)) in
             Some (List.map (fun tp -> view tp.tp_bound) me.mt_tparams,
                   List.map (fun (_, pt) -> view pt) me.mt_params,
                   view me.mt_return)
         | None ->
             match class_decl_of p i with
             | None -> None
             | Some ce ->
                 let (parent_cr, parent_decl_args) = ce.cl_parent in
                 let parent_args' = List.map (subst_typaram args) parent_decl_args in
                 lookup_method_on ~resolve p methods parent_cr parent_args' ml)

type demand_opts = {
    do_resolve_sigs : bool;
    do_scoped_bounds : bool;
    do_approx_fields : bool;
}

let legacy_demand_opts =
    { do_resolve_sigs = false; do_scoped_bounds = false; do_approx_fields = false }

let demand_opts_of (config : config) =
    { do_resolve_sigs = config.resolve_method_sigs;
      do_scoped_bounds = config.scoped_bounds;
      do_approx_fields = config.approx_field_reads }

let approx_field_type = function
    | Wild (Covariant, b) -> b
    | Wild (_, _) -> TyClass (Prelude "Object", [])
    | t -> t

let demand_bounds p d =
    match IntSet.min_elt_opt (tvars_in_demand d) with
    | Some tv -> scope_bounds p tv
    | None -> []

let demand_mbounds p assignment d =
    match IntSet.min_elt_opt (tvars_in_demand d) with
    | Some tv -> List.map (resolve_type assignment) (method_bounds p tv)
    | None -> []

let rec cartesian = function
    | [] -> [[]]
    | xs :: rest ->
        let tl = cartesian rest in
        List.concat_map (fun x -> List.map (fun r -> x :: r) tl) xs

let check_demand ?(opts = legacy_demand_opts) p assignment fl_map ml_map d =
    Generator.check_term_deadline ();
    let bounds = if opts.do_scoped_bounds then demand_bounds p d else [] in
    let mbounds = demand_mbounds p assignment d in
    let sub = is_subtype ~bounds ~mbounds p in
    match d with
    | FieldCount (t, k) ->
        (match resolve_type assignment t with
         | TyClass (cr, args) -> List.length (fields_of_class p cr args) = k
         | _ -> false)
    | Subtype (a, b) ->
        sub (resolve_type assignment a) (resolve_type assignment b)
    | NeedField (recv, fl, res) ->
        (match resolve_type assignment recv with
         | TyClass (cr, args) ->
             let fields = fields_of_class p cr args in
             (match List.assoc_opt fl fl_map with
              | None -> false
              | Some prog_fl ->
                  (match List.assoc_opt prog_fl fields with
                   | None -> false
                   | Some ft ->
                       let res' = resolve_type assignment res in
                       let ft = if opts.do_approx_fields
                           then approx_field_type ft else ft in
                       type_equal ft res'))
         | _ -> false)
    | NeedMethod (recv, ml, param_types, ret) ->
        (match resolve_type assignment recv with
         | TyClass (cr, args) ->
             (match List.assoc_opt ml ml_map with
              | None -> false
              | Some prog_ml ->
                  let resolve = if opts.do_resolve_sigs
                      then resolve_type assignment else Fun.id in
                  match lookup_method_on ~resolve p p.methods cr args prog_ml with
                  | None -> false
                  | Some (tbounds, mt_params, mt_ret) ->
                      let ret' = resolve_type assignment ret in
                      let args' = List.map (resolve_type assignment) param_types in
                      let fits sigma =
                          let inst = subst_ivars sigma in
                          type_equal (inst mt_ret) ret'
                          && List.for_all2 (fun a f -> sub a (inst f)) args' mt_params
                          && List.for_all (fun (j, b) -> sub (inst (ivar j)) (inst b))
                                 (List.mapi (fun j b -> (j, b)) tbounds) in
                      List.length param_types = List.length mt_params
                      && (if tbounds = [] then fits []
                          else
                              let cons = List.fold_left2 (fun acc f a ->
                                  collect_ivars f a acc)
                                  (collect_ivars mt_ret ret' []) mt_params args' in
                              let options = List.mapi (fun j _ ->
                                  match List.sort_uniq compare (List.filter_map
                                      (fun (k, t) -> if k = j then Some (j, t) else None)
                                      cons) with
                                  | [] -> [(j, TyClass (Prelude "Object", []))]
                                  | l -> l) tbounds in
                              List.exists fits (cartesian options)))
         | _ -> false)
    | TparamBound _ -> true

let check_demands ?opts p assignment fl_map ml_map ds =
    List.for_all (check_demand ?opts p assignment fl_map ml_map) ds

let check_label_neqs fl_map ml_map neqs =
    List.for_all (fun neq -> match neq with
        | (LField, l1, l2) ->
            let r1 = match List.assoc_opt l1 fl_map with Some v -> v | None -> l1 in
            let r2 = match List.assoc_opt l2 fl_map with Some v -> v | None -> l2 in
            r1 <> r2
        | (LMethod, l1, l2) ->
            let r1 = match List.assoc_opt l1 ml_map with Some v -> v | None -> l1 in
            let r2 = match List.assoc_opt l2 ml_map with Some v -> v | None -> l2 in
            r1 <> r2
    ) neqs

let fl_mapping_options p assignment demands =
    let fl_needs = List.filter_map (fun d -> match d with
        | NeedField (recv, fl, _) ->
            (match resolve_type assignment recv with
             | TyClass (cr, args) ->
                 let fields = fields_of_class p cr args in
                 Some (fl, List.map fst fields)
             | _ -> None)
        | _ -> None
    ) demands in
    let fl_needs = List.sort_uniq compare fl_needs in
    List.map (fun (fl, prog_fls) ->
        List.map (fun pfl -> (fl, pfl)) prog_fls
    ) fl_needs

let ml_mapping_options p assignment demands =
    let rec visible_mls cr =
        let synth_here = List.filter_map (fun me ->
            if is_subtype_cr p cr (Synth me.mt_class)
            then Some me.mt_label else None
        ) p.methods in
        let prelude_here = match cr with
            | Prelude n ->
                let own = prelude_methods_on n in
                let from_parent = match prelude_parent n with
                    | None -> []
                    | Some par -> visible_mls par in
                own @ from_parent
            | Synth i ->
                (match class_decl_of p i with
                 | None -> []
                 | Some ce -> visible_mls (fst ce.cl_parent))
        in
        synth_here @ prelude_here
    in
    let ml_needs = List.filter_map (fun d -> match d with
        | NeedMethod (recv, ml, _, _) ->
            (match resolve_type assignment recv with
             | TyClass (cr, _) ->
                 Some (ml, List.sort_uniq compare (visible_mls cr))
             | _ -> None)
        | _ -> None
    ) demands in
    let ml_needs = List.sort_uniq compare ml_needs in
    List.map (fun (ml, prog_mls) ->
        List.map (fun pml -> (ml, pml)) prog_mls
    ) ml_needs

let rec resolve_sterm assignment fl_map ml_map = function
    | SFree id -> Var id
    | SBound i -> BVar i
    | SNew (ty, args) ->
        New (resolve_type assignment ty,
             List.map (resolve_sterm assignment fl_map ml_map) args)
    | SFieldAccess (e, fl) ->
        let prog_fl = match List.assoc_opt fl fl_map with
            | Some p -> p | None -> fl in
        FieldAccess (resolve_sterm assignment fl_map ml_map e, prog_fl)
    | SMethodInvoke (e, ml, args) ->
        let prog_ml = match List.assoc_opt ml ml_map with
            | Some p -> p | None -> ml in
        MethodInvoke (resolve_sterm assignment fl_map ml_map e, prog_ml,
                      List.map (resolve_sterm assignment fl_map ml_map) args)
    | SLambda (ty, body) ->
        Lambda (resolve_type assignment ty,
                resolve_sterm assignment fl_map ml_map body)
    | SNull ty -> Null (resolve_type assignment ty)
    | SCond (c, t, e) ->
        Cond (resolve_sterm assignment fl_map ml_map c,
              resolve_sterm assignment fl_map ml_map t,
              resolve_sterm assignment fl_map ml_map e)

let render_cmethod (m : concrete_method) =
    let tparams_str =
        if m.cm_tparams = [] then ""
        else
            "<" ^ String.concat ", " (List.mapi (fun i tp ->
                let base = "X" ^ string_of_int i in
                if type_equal tp.tp_bound (TyClass (Prelude "Object", []))
                then base else base ^ " extends " ^ string_of_type tp.tp_bound
            ) m.cm_tparams) ^ "> "
    in
    let params_s = String.concat ", " (List.map (fun (sid, pt) ->
        string_of_type pt ^ " x" ^ string_of_int sid) m.cm_params) in
    tparams_str ^ string_of_type m.cm_return ^ " " ^ ml_name m.cm_label ^
    "(" ^ params_s ^ ") { return " ^ string_of_term m.cm_body ^ "; }"

let render_class cmethods assignment ce =
    let tparams_str =
        if ce.cl_tparams = [] then ""
        else
            let object_bound = TyClass (Prelude "Object", []) in
            "<" ^ String.concat ", " (List.mapi (fun i tp ->
                let base = string_of_variance tp.tp_variance ^ "P" ^ string_of_int i in
                if type_equal tp.tp_bound object_bound then base
                else base ^ " extends " ^ string_of_type tp.tp_bound
            ) ce.cl_tparams) ^ ">"
    in
    let (pcr, pargs) = ce.cl_parent in
    let parent_str =
        let args_str = if pargs = [] then ""
            else "<" ^ String.concat ", " (List.map string_of_type pargs) ^ ">" in
        " extends " ^ string_of_class_ref pcr ^ args_str
    in
    let fields_str = String.concat " " (List.map (fun (fl, ft) ->
        string_of_type (resolve_type assignment ft) ^ " " ^ fl_name fl ^ ";"
    ) ce.cl_fields) in
    let class_methods = List.filter (fun (m : concrete_method) ->
        m.cm_class = ce.cl_label) cmethods in
    let methods_str = String.concat " " (List.map render_cmethod class_methods) in
    let inner =
        match fields_str, methods_str with
        | "", "" -> ""
        | f, "" -> " " ^ f
        | "", m -> " " ^ m
        | f, m -> " " ^ f ^ " " ^ m
    in
    "class " ^ string_of_class_ref (Synth ce.cl_label) ^ tparams_str ^
    parent_str ^ " {" ^ inner ^ " }"

let concretize_classes assignment p =
    List.map (fun ce ->
        { cc_label = ce.cl_label;
          cc_tparams = ce.cl_tparams;
          cc_parent = (fst ce.cl_parent,
                       List.map (resolve_type assignment) (snd ce.cl_parent));
          cc_fields = List.map (fun (fl, ft) ->
              (fl, resolve_type assignment ft)) ce.cl_fields }
    ) p.classes

let is_generic_synth_new p cr args =
    match cr with
    | Synth i -> args <> [] &&
        (match class_decl_of p i with Some ce -> ce.cl_tparams <> [] | None -> false)
    | _ -> false

let rec diamondize_all ?(keep = fun () -> false) p = function
    | New (TyClass (cr, args), sub) when is_generic_synth_new p cr args && not (keep ()) ->
        New (TyClass (cr, List.mapi (fun i _ -> Hole i) args),
             List.map (diamondize_all ~keep p) sub)
    | New (ty, sub) -> New (ty, List.map (diamondize_all ~keep p) sub)
    | FieldAccess (e, fl) -> FieldAccess (diamondize_all ~keep p e, fl)
    | MethodInvoke (e, ml, sub) ->
        MethodInvoke (diamondize_all ~keep p e, ml, List.map (diamondize_all ~keep p) sub)
    | Cond (c, a, b) ->
        Cond (diamondize_all ~keep p c, diamondize_all ~keep p a, diamondize_all ~keep p b)
    | If (ty, c, a, b) ->
        If (ty, diamondize_all ~keep p c, diamondize_all ~keep p a, diamondize_all ~keep p b)
    | Lambda (pt, b) -> Lambda (pt, diamondize_all ~keep p b)
    | (Var _ | BVar _ | Null _) as x -> x

let maybe_diamond ?keep p diamond t = if diamond then diamondize_all ?keep p t else t

let explicit_keeper salt =
    let n = ref 0 in
    fun () -> incr n; Hashtbl.hash (salt, !n) land 3 = 0

let specialize_method class_tparams (m : concrete_method) : concrete_method =
    match m.cm_body, m.cm_params with
    | Var sym, params when List.mem_assoc sym params && m.cm_tparams = [] ->
        let pty = List.assoc sym params in
        (match pty with
         | TyClass _ ->
             { m with
               cm_tparams = [{ tp_variance = Invariant; tp_bound = pty }];
               cm_params = List.map (fun (s, t) ->
                   if s = sym then (s, MTParam 0) else (s, t)) params;
               cm_return = MTParam 0 }
         | TyParam k ->
             (match List.nth_opt class_tparams k with
              | Some { tp_bound = TyParam j; _ } when j <> k ->
                  { m with cm_return = TyParam j }
              | _ -> m)
         | _ -> m)
    | _ -> m

let concretize_methods ?(generic = false) ?keep
        ~diamond assignment fl_map ml_map p =
    List.map (fun me ->
        let class_tparams = match class_decl_of p me.mt_class with
            | Some ce -> ce.cl_tparams | None -> [] in
        (if generic then Fun.id else specialize_method class_tparams)
        { cm_class = me.mt_class;
          cm_label = me.mt_label;
          cm_this_sym = me.mt_this_sym;
          cm_tparams = List.map (fun tp ->
              { tp with tp_bound = resolve_type assignment tp.tp_bound }) me.mt_tparams;
          cm_params = List.map (fun (sid, pt) ->
              (sid, resolve_type assignment pt)) me.mt_params;
          cm_return = resolve_type assignment me.mt_return;
          cm_body = maybe_diamond ?keep p diamond
              (resolve_sterm assignment fl_map ml_map me.mt_body.sterm);
          cm_default = None }
    ) p.methods

let build_tagged_fact_for ?(diamond=false) ?(generic=false) ?(explicit_news=false)
        ?(salt=0) ?keep p e assignment fl_map ml_map =
    let keep = match keep with
        | Some _ -> keep
        | None ->
            if explicit_news && diamond
            then Some (explicit_keeper
                (salt, Hashtbl.hash_param 64 256 (assignment, fl_map, ml_map)))
            else None in
    let cmethods = concretize_methods ~generic ?keep ~diamond assignment fl_map ml_map p in
    let buf = Buffer.create 256 in
    List.iter (fun ce ->
        Buffer.add_string buf (render_class cmethods assignment ce);
        Buffer.add_char buf '\n'
    ) (List.rev p.classes);
    let main_term = maybe_diamond ?keep p diamond
        (resolve_sterm assignment fl_map ml_map e.sterm) in
    let main_type = resolve_type assignment e.styp in
    Buffer.add_string buf ("main: " ^ string_of_term main_term ^
                           " : " ^ string_of_type main_type);
    let bindings = IntMap.fold (fun sid info acc ->
        (sid, resolve_type assignment info.sym_type) :: acc
    ) e.sym_map [] in
    {
        tf_classes = concretize_classes assignment p;
        tf_methods = cmethods;
        tf_main_term = main_term;
        tf_main_type = main_type;
        tf_bindings = List.sort (fun (a, _) (b, _) -> compare a b) bindings;
        tf_rendered = Buffer.contents buf;
    }

let candidate_groundings ?cap ?(fixed=[]) ?(randomize=false) config p =
    let cap = match cap with Some c -> c | None -> config.assignment_cap in
    let tvars = IntSet.elements (tvars_in_program p) in
    if List.length tvars > config.max_tvars then Seq.empty
    else
        let cache = Hashtbl.create 4 in
        let candidates_for tv =
            let scope = match IntMap.find_opt tv p.tvar_scope with
                | Some n -> n | None -> 0 in
            let bounds = if config.scoped_bounds then scope_bounds p tv else [] in
            let mtparams = List.length (method_bounds p tv) in
            match Hashtbl.find_opt cache (scope, bounds, mtparams) with
            | Some c -> c
            | None ->
                let c = types_up_to ~bounds ~mtparams ~randomize
                    ~multi_wild:config.multi_wildcards
                    p ~scope_tparams:scope config.max_type_depth in
                Hashtbl.replace cache (scope, bounds, mtparams) c; c
        in
        let assignment_options = List.map (fun tv ->
            match List.assoc_opt tv fixed with
            | Some ct -> [(tv, ct)]
            | None ->
                let cands = List.map (fun ct -> (tv, ct)) (candidates_for tv) in
                if randomize then shuffle cands else cands
        ) tvars in
        seq_product assignment_options
        |> Seq.take cap
        |> Seq.concat_map (fun assignment ->
            Generator.check_term_deadline ();
            seq_product (fl_mapping_options p assignment p.all_demands)
            |> Seq.concat_map (fun fl_map ->
                seq_product (ml_mapping_options p assignment p.all_demands)
                |> Seq.map (fun ml_map -> (assignment, fl_map, ml_map))))

let budget_take search_budget seq =
    match search_budget with Some b -> Seq.take b seq | None -> seq

let instantiate_program ~search_budget config p : tagged_fact Seq.t =
    match p.main with
    | None -> Seq.empty
    | Some e ->
        candidate_groundings ~randomize:(search_budget <> None) config p
        |> budget_take search_budget
        |> Seq.filter (fun (assignment, fl_map, ml_map) ->
            Generator.check_term_deadline ();
            check_demands ~opts:(demand_opts_of config)
                p assignment fl_map ml_map p.all_demands
            && check_label_neqs fl_map ml_map p.all_label_neqs)
        |> Seq.map (fun (assignment, fl_map, ml_map) ->
            let salt = if config.explicit_news && search_budget <> None
                then Random.bits () else 0 in
            build_tagged_fact_for ~diamond:true ~generic:config.generic_methods
                ~explicit_news:config.explicit_news ~salt p e assignment fl_map ml_map)

let default_object_sterm = SNew (TyClass (Prelude "Object", []), [])

let rec close_sterm bound = function
    | SFree id when IntSet.mem id bound -> SFree id
    | SFree _ -> default_object_sterm
    | SBound i -> SBound i
    | SNew (typ, args) -> SNew (typ, List.map (close_sterm bound) args)
    | SFieldAccess (e, fl) -> SFieldAccess (close_sterm bound e, fl)
    | SMethodInvoke (e, ml, args) ->
        SMethodInvoke (close_sterm bound e, ml,
                       List.map (close_sterm bound) args)
    | SLambda (typ, body) -> SLambda (typ, close_sterm bound body)
    | SCond (c, t, e) ->
        SCond (close_sterm bound c, close_sterm bound t, close_sterm bound e)
    | SNull _ as t -> t

let close_expr_proto_term ~bound (e : expr_proto_term) : expr_proto_term =
    { e with
      sterm = close_sterm bound e.sterm;
      sym_map = IntMap.filter (fun id _ -> IntSet.mem id bound) e.sym_map }

let method_bound_syms (m : method_entry) : IntSet.t =
    List.fold_left (fun acc (sym_id, _) -> IntSet.add sym_id acc)
        (IntSet.singleton m.mt_this_sym) m.mt_params

let close_program (p : program_proto_term) : program_proto_term =
    let main' = match p.main with
        | None -> Some (make_prelude_new "Object")
        | Some e -> Some (close_expr_proto_term ~bound:IntSet.empty e)
    in
    let methods' = List.map (fun m ->
        { m with mt_body = close_expr_proto_term ~bound:(method_bound_syms m) m.mt_body }
    ) p.methods in
    { p with main = main'; methods = methods' }

let auto_close_if_needed config = function
    | ProgramProtoTerm p when config.auto_close -> ProgramProtoTerm (close_program p)
    | s -> s

let concretize ~search_budget config s =
    match auto_close_if_needed config s with
    | ExprProtoTerm _ | FaultedProgram _ -> Seq.empty
    | ProgramProtoTerm p -> instantiate_program ~search_budget config p

let grounding_steps ?(fixed=[]) config p =
    let tvars = IntSet.elements (tvars_in_program p) in
    if List.length tvars > config.max_tvars then Seq.empty
    else fun () ->
        let cache = Hashtbl.create 4 in
        let candidates_for tv =
            let scope = match IntMap.find_opt tv p.tvar_scope with
                | Some n -> n | None -> 0 in
            let bounds = if config.scoped_bounds then scope_bounds p tv else [] in
            let mtparams = List.length (method_bounds p tv) in
            match Hashtbl.find_opt cache (scope, bounds, mtparams) with
            | Some c -> c
            | None ->
                let c = types_up_to ~all:true ~bounds ~mtparams
                    ~multi_wild:config.multi_wildcards
                    p ~scope_tparams:scope config.max_type_depth in
                Hashtbl.replace cache (scope, bounds, mtparams) c; c in
        let dims = List.map (fun tv ->
            match List.assoc_opt tv fixed with
            | Some ct -> [| (tv, ct) |]
            | None -> Array.of_list (List.map (fun ct -> (tv, ct)) (candidates_for tv))
        ) tvars in
        let nonempty seq = fun () ->
            match seq () with Seq.Nil -> Seq.Cons (None, Seq.empty) | c -> c in
        (diag_product dims
         |> Seq.concat_map (fun assignment ->
             nonempty (
                 seq_product (fl_mapping_options p assignment p.all_demands)
                 |> Seq.concat_map (fun fl_map ->
                     seq_product (ml_mapping_options p assignment p.all_demands)
                     |> Seq.map (fun ml_map -> Some (assignment, fl_map, ml_map)))))) ()

let max_mask_bits = 8

let facts_all_masks config p e assignment fl_map ml_map =
    let build keep =
        build_tagged_fact_for ~diamond:true ~generic:config.generic_methods
            ~keep p e assignment fl_map ml_map in
    if not config.explicit_news then Seq.return (build (fun () -> false))
    else
        let count = ref 0 in
        let first = build (fun () -> incr count; false) in
        let k = min !count max_mask_bits in
        Seq.cons first (Seq.init ((1 lsl k) - 1) (fun m ->
            let mask = m + 1 and c = ref 0 in
            build (fun () ->
                let b = !c in incr c; b < k && (mask lsr b) land 1 = 1)))

let instantiate_steps config p : tagged_fact option Seq.t =
    match p.main with
    | None -> Seq.empty
    | Some e ->
        grounding_steps config p
        |> Seq.concat_map (function
          | None -> Seq.return None
          | Some (assignment, fl_map, ml_map) ->
            if check_demands ~opts:(demand_opts_of config)
                   p assignment fl_map ml_map p.all_demands
               && check_label_neqs fl_map ml_map p.all_label_neqs
            then Seq.map Option.some (facts_all_masks config p e assignment fl_map ml_map)
            else Seq.return None)

let concretize_steps config s =
    match auto_close_if_needed config s with
    | ExprProtoTerm _ | FaultedProgram _ -> Seq.empty
    | ProgramProtoTerm p -> instantiate_steps config p
