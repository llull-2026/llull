open HephPrograms
open Heph2Prototerms

let types_up_to p ~scope_tparams depth =
    let tparams = List.init scope_tparams (fun i -> TyParam i) in
    let prelude_nongeneric = List.filter_map (fun pd ->
        if prelude_tparam_variances pd.pr_name = []
        then Some (TyClass (Prelude pd.pr_name, []))
        else None
    ) prelude in
    let synth_nongeneric = List.filter_map (fun ce ->
        if ce.cl_tparams = [] then Some (TyClass (Synth ce.cl_label, []))
        else None
    ) p.classes in
    let depth0 = prelude_nongeneric @ tparams @ synth_nongeneric in
    let rec up_to d =
        if d = 0 then depth0
        else
            let lower = up_to (d - 1) in
            let prelude_generic_instances = List.concat_map (fun pd ->
                let n = List.length (prelude_tparam_variances pd.pr_name) in
                if n = 0 then []
                else
                    let arg_tuples = capped_tuples lower n in
                    List.map (fun args -> TyClass (Prelude pd.pr_name, args))
                        arg_tuples
            ) prelude in
            let synth_generic_instances = List.concat_map (fun ce ->
                let n = List.length ce.cl_tparams in
                if n = 0 then []
                else
                    let arg_tuples = capped_tuples lower n in
                    List.filter_map (fun args ->
                        if bound_satisfied p (Synth ce.cl_label) args
                        then Some (TyClass (Synth ce.cl_label, args))
                        else None
                    ) arg_tuples
            ) p.classes in
            lower @ prelude_generic_instances @ synth_generic_instances
    in
    up_to depth

let rec resolve_type assignment = function
    | TyClass (cr, args) ->
        TyClass (cr, List.map (resolve_type assignment) args)
    | TVar i ->
        (match List.assoc_opt i assignment with
         | Some t -> t
         | None -> TyClass (Prelude "Object", []))
    | TyParam _ as t -> t
    | TyBot -> TyBot

let rec lookup_method_on p methods cr args ml =
    match cr with
    | Prelude n ->
        (match prelude_method_signature n ml with
         | Some (params, ret) ->
             Some (List.map (subst_typaram args) params,
                   subst_typaram args ret)
         | None ->
             match prelude_parent n with
             | None -> None
             | Some par -> lookup_method_on p methods par [] ml)
    | Synth i ->
        (match List.find_opt (fun me ->
            me.mt_class = i && me.mt_label = ml) methods with
         | Some me ->
             let params' = List.map (fun (_, pt) -> subst_typaram args pt) me.mt_params in
             let ret' = subst_typaram args me.mt_return in
             Some (params', ret')
         | None ->
             match class_decl_of p i with
             | None -> None
             | Some ce ->
                 let (parent_cr, parent_decl_args) = ce.cl_parent in
                 let parent_args' = List.map (subst_typaram args) parent_decl_args in
                 lookup_method_on p methods parent_cr parent_args' ml)

let check_demand p assignment fl_map ml_map d =
    match d with
    | FieldCount (t, k) ->
        (match resolve_type assignment t with
         | TyClass (cr, args) -> List.length (fields_of_class p cr args) = k
         | _ -> false)
    | Subtype (a, b) ->
        is_subtype p (resolve_type assignment a) (resolve_type assignment b)
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
                       type_equal ft res'))
         | _ -> false)
    | NeedMethod (recv, ml, param_types, ret) ->
        (match resolve_type assignment recv with
         | TyClass (cr, args) ->
             (match List.assoc_opt ml ml_map with
              | None -> false
              | Some prog_ml ->
                  match lookup_method_on p p.methods cr args prog_ml with
                  | None -> false
                  | Some (mt_params, mt_ret) ->
                      let ret' = resolve_type assignment ret in
                      List.length param_types = List.length mt_params
                      && type_equal mt_ret ret'
                      && List.for_all2 (fun call_pt meth_pt ->
                             is_subtype p
                                 (resolve_type assignment call_pt) meth_pt
                         ) param_types mt_params)
         | _ -> false)
    | TparamBound _ -> true

let check_demands p assignment fl_map ml_map ds =
    List.for_all (check_demand p assignment fl_map ml_map) ds

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
    | SIf (ty, c, t, e) ->
        If (resolve_type assignment ty,
            resolve_sterm assignment fl_map ml_map c,
            resolve_sterm assignment fl_map ml_map t,
            resolve_sterm assignment fl_map ml_map e)

let render_method assignment fl_map ml_map me =
    let ret_s = string_of_type (resolve_type assignment me.mt_return) in
    let params_s = String.concat ", " (List.map (fun (sid, pt) ->
        string_of_type (resolve_type assignment pt) ^ " x" ^ string_of_int sid
    ) me.mt_params) in
    let body_term = resolve_sterm assignment fl_map ml_map me.mt_body.sterm in
    ret_s ^ " " ^ ml_name me.mt_label ^ "(" ^ params_s ^ ") { return " ^
    string_of_term body_term ^ "; }"

let render_class p assignment fl_map ml_map ce =
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
    let class_methods = List.filter (fun me ->
        me.mt_class = ce.cl_label) p.methods in
    let methods_str = String.concat " "
        (List.map (render_method assignment fl_map ml_map) class_methods) in
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

let concretize_methods assignment fl_map ml_map p =
    List.map (fun me ->
        { cm_class = me.mt_class;
          cm_label = me.mt_label;
          cm_this_sym = me.mt_this_sym;
          cm_params = List.map (fun (sid, pt) ->
              (sid, resolve_type assignment pt)) me.mt_params;
          cm_return = resolve_type assignment me.mt_return;
          cm_body = resolve_sterm assignment fl_map ml_map me.mt_body.sterm }
    ) p.methods

let build_tagged_fact_for p e assignment fl_map ml_map =
    let buf = Buffer.create 256 in
    List.iter (fun ce ->
        Buffer.add_string buf
            (render_class p assignment fl_map ml_map ce);
        Buffer.add_char buf '\n'
    ) (List.rev p.classes);
    let main_term = resolve_sterm assignment fl_map ml_map e.sterm in
    let main_type = resolve_type assignment e.styp in
    Buffer.add_string buf ("main: " ^ string_of_term main_term ^
                           " : " ^ string_of_type main_type);
    let bindings = IntMap.fold (fun sid info acc ->
        (sid, resolve_type assignment info.sym_type) :: acc
    ) e.sym_map [] in
    {
        tf_classes = concretize_classes assignment p;
        tf_methods = concretize_methods assignment fl_map ml_map p;
        tf_main_term = main_term;
        tf_main_type = main_type;
        tf_bindings = List.sort (fun (a, _) (b, _) -> compare a b) bindings;
        tf_rendered = Buffer.contents buf;
    }

let candidate_groundings ?cap ?(fixed=[]) config p =
    let cap = match cap with Some c -> c | None -> config.assignment_cap in
    let tvars = IntSet.elements (tvars_in_program p) in
    if List.length tvars > config.max_tvars then Seq.empty
    else
        let candidates_for tv =
            let scope = match IntMap.find_opt tv p.tvar_scope with
                | Some n -> n | None -> 0 in
            types_up_to p ~scope_tparams:scope config.max_type_depth
        in
        let assignment_options = List.map (fun tv ->
            match List.assoc_opt tv fixed with
            | Some ct -> [(tv, ct)]
            | None -> List.map (fun ct -> (tv, ct)) (candidates_for tv)
        ) tvars in
        seq_product assignment_options
        |> Seq.take cap
        |> Seq.concat_map (fun assignment ->
            seq_product (fl_mapping_options p assignment p.all_demands)
            |> Seq.concat_map (fun fl_map ->
                seq_product (ml_mapping_options p assignment p.all_demands)
                |> Seq.map (fun ml_map -> (assignment, fl_map, ml_map))))

let budget_take search_budget seq =
    match search_budget with Some b -> Seq.take b seq | None -> seq

exception Solve_fail

type solve_state = {
    sp : program_proto_term;
    subst : (int * heph_type) list;
    sfl : (int * field_label) list;
    sml : (int * method_label) list;
}

let solve_default_ty = TyClass (Prelude "Object", [])

let sderef subst t =
    let rec go seen t =
        match t with
        | TVar i when not (List.mem i seen) ->
            (match List.assoc_opt i subst with Some t' -> go (i :: seen) t' | None -> t)
        | TVar _ -> t
        | TyClass (cr, args) -> TyClass (cr, List.map (go seen) args)
        | t -> t
    in go [] t

let bind_tv st i t = { st with subst = (i, t) :: st.subst }

let rec ground subst t =
    match sderef subst t with
    | TyClass (cr, args) -> TyClass (cr, List.map (ground subst) args)
    | TVar _ -> solve_default_ty
    | other -> other

let ground_assignment st =
    List.map (fun (i, _) -> (i, ground st.subst (TVar i))) st.subst

let bind_if_free st ty =
    match sderef st.subst ty with TVar i -> bind_tv st i solve_default_ty | _ -> st

let demand_recv = function
    | NeedField (r, _, _) | NeedMethod (r, _, _, _) -> Some r
    | _ -> None

let mint_class_bind st i =
    let label = st.sp.next_class_label in
    let ce = { cl_label = label; cl_tparams = [];
               cl_parent = (Prelude "Object", []); cl_fields = [] } in
    { st with
      sp = { st.sp with classes = st.sp.classes @ [ce];
             next_class_label = label + 1 };
      subst = (i, TyClass (Synth label, [])) :: st.subst }

let alloc_fl st fl_abstract =
    match List.assoc_opt fl_abstract st.sfl with
    | Some fl -> (fl, st)
    | None ->
        let fl = st.sp.next_fl in
        (fl, { st with sp = { st.sp with next_fl = fl + 1 };
                       sfl = (fl_abstract, fl) :: st.sfl })

let ensure_field st c fl fty =
    let present = List.exists (fun ce ->
        ce.cl_label = c && List.mem_assoc fl ce.cl_fields) st.sp.classes in
    if present then st
    else
        { st with sp = { st.sp with classes = List.map (fun ce ->
            if ce.cl_label = c then { ce with cl_fields = ce.cl_fields @ [(fl, fty)] }
            else ce) st.sp.classes } }

let alloc_ml st ml_abstract =
    match List.assoc_opt ml_abstract st.sml with
    | Some ml -> (ml, st)
    | None ->
        let ml = st.sp.next_ml in
        (ml, { st with sp = { st.sp with next_ml = ml + 1 };
                       sml = (ml_abstract, ml) :: st.sml })

let rec trivial_term ?(fuel = 16) p ty =
    match ty with
    | TyClass (cr, args) when fuel > 0 ->
        SNew (ty, List.map (fun (_, ft) -> trivial_term ~fuel:(fuel - 1) p ft)
                    (fields_of_class p cr args))
    | _ -> SNew (TyClass (Prelude "Object", []), [])

let trivial_body p ty : expr_proto_term =
    { sterm = trivial_term p ty; styp = ty; sym_map = IntMap.empty;
      demands = []; label_neqs = [];
      next_tvar = 0; next_sym = 0; next_fl = 0; next_ml = 0 }

let ensure_method st c ml param_tys ret_t =
    let present = List.exists (fun me ->
        me.mt_class = c && me.mt_label = ml) st.sp.methods in
    if present then st
    else
        let me = { mt_class = c; mt_label = ml; mt_this_sym = 0;
                   mt_params = List.mapi (fun i pt -> (i + 1, pt)) param_tys;
                   mt_return = ret_t; mt_body = trivial_body st.sp ret_t } in
        { st with sp = { st.sp with methods = me :: st.sp.methods } }

let object_ty = TyClass (Prelude "Object", [])
let invariant_tparam = { tp_variance = Invariant; tp_bound = object_ty }
let prelude_insts =
    List.map (fun n -> TyClass (Prelude n, []))
        ["Object"; "Number"; "Integer"; "String"; "Boolean"]

let mint_class ?(tparams = []) ?(fields = []) st =
    let label = st.sp.next_class_label in
    let ce = { cl_label = label; cl_tparams = tparams;
               cl_parent = (Prelude "Object", []); cl_fields = fields } in
    (label, { st with sp = { st.sp with classes = st.sp.classes @ [ce];
                             next_class_label = label + 1 } })

let bind_ret st ret t =
    match sderef st.subst ret with
    | TVar j -> bind_tv st j t
    | rt -> if type_equal rt t then st else raise Solve_fail

let try_branch f = try Some (f ()) with Solve_fail -> None

let add_method_record st c ml param_tys ret_t body sml_entry =
    { st with
      sp = { st.sp with
             methods = { mt_class = c; mt_label = ml; mt_this_sym = 0;
                         mt_params = List.mapi (fun i pt -> (i + 1, pt)) param_tys;
                         mt_return = ret_t; mt_body = body } :: st.sp.methods;
             next_ml = ml + 1 };
      sml = sml_entry :: st.sml }

let solve_method st recv ma args ret : solve_state Seq.t =
    match List.assoc_opt ma st.sml with
    | Some ml ->
        (match sderef st.subst recv with
         | TyClass (Synth c, _) ->
             let st = bind_if_free st ret in
             let st = List.fold_left bind_if_free st args in
             Seq.return (ensure_method st c ml
                 (List.map (sderef st.subst) args) (sderef st.subst ret))
         | _ -> Seq.empty)
    | None ->
        match sderef st.subst recv with
        | TyClass (Synth c, _) ->
            let st = bind_if_free st ret in
            let st = List.fold_left bind_if_free st args in
            let ret_t = sderef st.subst ret in
            let ptys = List.map (sderef st.subst) args in
            let ml = st.sp.next_ml in
            Seq.return (add_method_record st c ml ptys ret_t
                (trivial_body st.sp ret_t) (ma, ml))
        | TVar i ->
            let mono () =
                let (c, st) = mint_class st in
                let st = bind_tv st i (TyClass (Synth c, [])) in
                let st = bind_if_free st ret in
                let st = List.fold_left bind_if_free st args in
                let ret_t = sderef st.subst ret in
                let ptys = List.map (sderef st.subst) args in
                add_method_record st c (st.sp.next_ml) ptys ret_t
                    (trivial_body st.sp ret_t) (ma, st.sp.next_ml) in
            let generic t () =
                let st = List.fold_left bind_if_free st args in
                let ptys = List.map (sderef st.subst) args in
                let fl = st.sp.next_fl in
                let st = { st with sp = { st.sp with next_fl = fl + 1 } } in
                let (c, st) = mint_class ~tparams:[invariant_tparam]
                                  ~fields:[(fl, TyParam 0)] st in
                let st = bind_tv st i (TyClass (Synth c, [t])) in
                let st = bind_ret st ret t in
                let body = { sterm = SFieldAccess (SFree 0, fl); styp = TyParam 0;
                             sym_map = IntMap.empty; demands = []; label_neqs = [];
                             next_tvar = 0; next_sym = 0; next_fl = 0; next_ml = 0 } in
                add_method_record st c (st.sp.next_ml) ptys (TyParam 0) body (ma, st.sp.next_ml) in
            List.to_seq
                (List.filter_map try_branch (mono :: List.map generic prelude_insts))
        | _ -> Seq.empty

let solve_field st recv fa res : solve_state Seq.t =
    match sderef st.subst recv with
    | TyClass (Synth c, _) ->
        let st = bind_if_free st res in
        let (fl, st) = alloc_fl st fa in
        Seq.return (ensure_field st c fl (sderef st.subst res))
    | TVar i ->
        let mono () =
            let (c, st) = mint_class st in
            let st = bind_tv st i (TyClass (Synth c, [])) in
            let st = bind_if_free st res in
            let (fl, st) = alloc_fl st fa in
            ensure_field st c fl (sderef st.subst res) in
        let generic t () =
            let (fl, st) = alloc_fl st fa in
            let (c, st) = mint_class ~tparams:[invariant_tparam]
                              ~fields:[(fl, TyParam 0)] st in
            let st = bind_tv st i (TyClass (Synth c, [t])) in
            bind_ret st res t in
        let covariant_field () =
            let (fl, st) = alloc_fl st fa in
            let (cc, st) = mint_class
                ~tparams:[{ tp_variance = Covariant; tp_bound = object_ty }] st in
            let cc_obj = TyClass (Synth cc, [object_ty]) in
            let (d, st) = mint_class ~fields:[(fl, cc_obj)] st in
            let st = bind_tv st i (TyClass (Synth d, [])) in
            bind_ret st res cc_obj in
        List.to_seq
            (List.filter_map try_branch
                (mono :: covariant_field :: List.map generic prelude_insts))
    | _ -> Seq.empty

let covariant_subtypes st sup =
    match sup with
    | TyClass (Synth c, [arg]) ->
        (match class_decl_of st.sp c with
         | Some ce when (match ce.cl_tparams with
                         | [{ tp_variance = Covariant; _ }] -> true | _ -> false) ->
             List.filter_map (fun sub ->
                 if not (type_equal sub arg) && is_subtype st.sp sub arg
                 then Some (TyClass (Synth c, [sub])) else None) prelude_insts
         | _ -> [])
    | _ -> []

let solve_subtype st a b : solve_state Seq.t =
    match sderef st.subst a, sderef st.subst b with
    | TVar i, db ->
        List.to_seq (bind_tv st i db
            :: List.map (fun sub -> bind_tv st i sub) (covariant_subtypes st db))
    | da, TVar i -> Seq.return (bind_tv st i da)
    | da, db -> if is_subtype st.sp da db then Seq.return st else Seq.empty

let solve_program p : solve_state Seq.t =
    let st0 = { sp = p; subst = []; sfl = []; sml = [] } in
    let after_members =
        List.fold_left (fun states d ->
            match d with
            | NeedField (r, fa, res) ->
                Seq.concat_map (fun st -> solve_field st r fa res) states
            | NeedMethod (r, ma, args, ret) ->
                Seq.concat_map (fun st -> solve_method st r ma args ret) states
            | _ -> states)
            (Seq.return st0) p.all_demands in
    List.fold_left (fun states d ->
        match d with
        | Subtype (a, b) -> Seq.concat_map (fun st -> solve_subtype st a b) states
        | _ -> states)
        after_members p.all_demands

let ensure_recv_class st recv =
    match sderef st.subst recv with
    | TyClass (Synth c, _) -> Some (c, st)
    | TVar i ->
        let (c, st) = mint_class st in
        Some (c, bind_tv st i (TyClass (Synth c, [])))
    | _ -> None

let integer_ty = TyClass (Prelude "Integer", [])

let violate_method_omit st recv args ret =
    let st = bind_if_free st ret in
    let st = List.fold_left bind_if_free st args in
    match sderef st.subst recv with
    | TVar i ->
        let (c, st) = mint_class st in
        Seq.return (bind_tv st i (TyClass (Synth c, [])))
    | _ -> Seq.return st

let violate_method_body st recv ma args ret =
    match sderef st.subst ret with
    | TVar j ->
        (match ensure_recv_class st recv with
         | None -> Seq.empty
         | Some (c, st) ->
             let st = List.fold_left bind_if_free st args in
             let st = bind_tv st j integer_ty in
             let ptys = List.map (sderef st.subst) args in
             let ml = st.sp.next_ml in
             let bad_body = trivial_body st.sp object_ty in
             Seq.return (add_method_record st c ml ptys integer_ty bad_body (ma, ml)))
    | _ -> Seq.empty

let violate_method_params st recv ma args ret =
    match args with
    | [] -> Seq.empty
    | _ ->
        (match ensure_recv_class st recv with
         | None -> Seq.empty
         | Some (c, st) ->
             let st = bind_if_free st ret in
             let st = List.fold_left bind_if_free st args in
             let ret_t = sderef st.subst ret in
             let arg_tys = List.map (sderef st.subst) args in
             match List.find_opt (fun t -> not (is_subtype st.sp (List.hd arg_tys) t))
                     prelude_insts with
             | None -> Seq.empty
             | Some wrong ->
                 let ptys = wrong :: List.tl arg_tys in
                 let ml = st.sp.next_ml in
                 Seq.return (add_method_record st c ml ptys ret_t
                     (trivial_body st.sp ret_t) (ma, ml)))

let violate_member st = function
    | NeedField (recv, _fa, res) ->
        let st = bind_if_free st res in
        (match sderef st.subst recv with
         | TVar i ->
             let (c, st) = mint_class st in
             Seq.return (bind_tv st i (TyClass (Synth c, [])))
         | _ -> Seq.return st)
    | NeedMethod (recv, ma, args, ret) ->
        List.fold_left Seq.append Seq.empty [
            violate_method_omit st recv args ret;
            violate_method_body st recv ma args ret;
            violate_method_params st recv ma args ret;
        ]
    | _ -> Seq.return st

let violate_subtype st a b =
    let mismatches against =
        List.filter_map (fun t ->
            if against t then None else Some t) prelude_insts in
    match sderef st.subst a, sderef st.subst b with
    | TVar i, db ->
        List.to_seq (List.map (bind_tv st i) (mismatches (fun t -> is_subtype st.sp t db)))
    | da, TVar i ->
        List.to_seq (List.map (bind_tv st i) (mismatches (fun t -> is_subtype st.sp da t)))
    | da, db -> if is_subtype st.sp da db then Seq.empty else Seq.return st

let solve_program_violating p target : solve_state Seq.t =
    let st0 = { sp = p; subst = []; sfl = []; sml = [] } in
    let _, after_members =
        List.fold_left (fun (i, states) d ->
            let step st =
                match d with
                | NeedField (r, fa, res) ->
                    if i = target then violate_member st d else solve_field st r fa res
                | NeedMethod (r, ma, args, ret) ->
                    if i = target then violate_member st d else solve_method st r ma args ret
                | _ -> Seq.return st in
            (i + 1, Seq.concat_map step states))
            (0, Seq.return st0) p.all_demands in
    let _, result =
        List.fold_left (fun (i, states) d ->
            let step st =
                match d with
                | Subtype (a, b) ->
                    if i = target then violate_subtype st a b else solve_subtype st a b
                | _ -> Seq.return st in
            (i + 1, Seq.concat_map step states))
            (0, after_members) p.all_demands in
    result

let trivial_main =
    { sterm = SNew (TyClass (Prelude "Object", []), []);
      styp = TyClass (Prelude "Object", []); sym_map = IntMap.empty;
      demands = []; label_neqs = [];
      next_tvar = 0; next_sym = 0; next_fl = 0; next_ml = 0 }

let type_assignments config st : (int * heph_type) list Seq.t =
    let all_tvars = IntSet.elements (tvars_in_program st.sp) in
    let free = List.filter (fun i ->
        match sderef st.subst (TVar i) with TVar _ -> true | _ -> false) all_tvars in
    if List.length free > config.max_tvars then Seq.empty
    else
        let options = List.map (fun i ->
            let scope = match IntMap.find_opt i st.sp.tvar_scope with
                | Some n -> n | None -> 0 in
            List.map (fun t -> (i, t))
                (types_up_to st.sp ~scope_tparams:scope config.max_type_depth)) free in
        seq_product options
        |> Seq.take config.assignment_cap
        |> Seq.map (fun free_assign ->
            let combined = st.subst @ free_assign in
            List.map (fun i -> (i, ground combined (TVar i))) all_tvars)

let instantiate_program ~search_budget:_ config p : tagged_fact Seq.t =
    match p.main with
    | None -> Seq.empty
    | Some e ->
    solve_program p
    |> Seq.concat_map (fun st ->
        type_assignments config st
        |> Seq.filter_map (fun assignment ->
            let f = build_tagged_fact_for st.sp e assignment st.sfl st.sml in
            if HephTypechecker.check f then Some f else None))

let add_bound_violation st =
    let c = st.sp.next_class_label in
    let bounded =
        { cl_label = c;
          cl_tparams = [{ tp_variance = Invariant; tp_bound = TyClass (Prelude "Number", []) }];
          cl_parent = (Prelude "Object", []); cl_fields = [] } in
    let d = c + 1 in
    let violating =
        { cl_label = d; cl_tparams = [];
          cl_parent = (Synth c, [TyClass (Prelude "String", [])]); cl_fields = [] } in
    { st with sp = { st.sp with classes = st.sp.classes @ [bounded; violating];
                     next_class_label = d + 1 } }

let instantiate_program_violating config p : tagged_fact Seq.t =
    match p.main with
    | None -> Seq.empty
    | Some e ->
        let render st =
            type_assignments config st
            |> Seq.filter_map (fun assignment ->
                let f = build_tagged_fact_for st.sp e assignment st.sfl st.sml in
                if HephTypechecker.check f then None else Some f) in
        let demand_targets =
            Seq.init (List.length p.all_demands) Fun.id
            |> Seq.concat_map (fun target ->
                solve_program_violating p target |> Seq.concat_map render) in
        let bound_targets =
            solve_program p |> Seq.concat_map (fun st -> render (add_bound_violation st)) in
        Seq.append demand_targets bound_targets

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
    | SIf (typ, c, t, e) ->
        SIf (typ, close_sterm bound c, close_sterm bound t, close_sterm bound e)

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
    match s with
    | ExprProtoTerm _ | FaultedProgram _ -> Seq.empty
    | ProgramProtoTerm p -> instantiate_program ~search_budget config p
