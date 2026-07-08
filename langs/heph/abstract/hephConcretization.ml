open HephPrograms
open HephPrototerms

type config = {
    auto_close     : bool;
    max_tvars      : int;
    max_type_depth : int;
    assignment_cap : int;
    max_identical_classes : int;
}

let parse_config kvs =
    let bool_of k default = match List.assoc_opt k kvs with
        | Some "true" -> true | Some "false" -> false | _ -> default in
    let int_of k default = match List.assoc_opt k kvs with
        | Some s -> (match int_of_string_opt s with Some i -> i | None -> default)
        | None -> default in
    { auto_close = bool_of "auto_close" true;
      max_tvars = int_of "max_tvars" 5;
      max_type_depth = int_of "max_type_depth" 1;
      assignment_cap = int_of "assignment_cap" 4096;
      max_identical_classes = int_of "max_identical_classes" 0 }

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

let instantiate_program ~search_budget config p : tagged_fact Seq.t =
    match p.main with
    | None -> Seq.empty
    | Some e ->
        candidate_groundings config p
        |> budget_take search_budget
        |> Seq.filter (fun (assignment, fl_map, ml_map) ->
            check_demands p assignment fl_map ml_map p.all_demands
            && check_label_neqs fl_map ml_map p.all_label_neqs)
        |> Seq.map (fun (assignment, fl_map, ml_map) ->
            build_tagged_fact_for p e assignment fl_map ml_map)

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
