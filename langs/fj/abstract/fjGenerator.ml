open FjPrograms
include FjPrototerms

let rec field_labels_in_sterm : proto_term -> IntSet.t = function
    | SFree _ -> IntSet.empty
    | SNew (_, args) -> List.fold_left (fun acc a -> IntSet.union acc (field_labels_in_sterm a)) IntSet.empty args
    | SFieldAccess (e, fl) -> IntSet.add fl (field_labels_in_sterm e)
    | SMethodInvoke (e, _, args) ->
        List.fold_left (fun acc a -> IntSet.union acc (field_labels_in_sterm a))
            (field_labels_in_sterm e) args

let field_labels_in_demands (ds : demand list) =
    List.fold_left (fun acc d ->
        match d with NeedField (_, fl, _) -> IntSet.add fl acc | _ -> acc
    ) IntSet.empty ds

let field_labels_in_prototerm (s : expr_prototerm) =
    IntSet.union (field_labels_in_sterm s.sterm) (field_labels_in_demands s.demands)

let rec method_labels_in_sterm : proto_term -> IntSet.t = function
    | SFree _ -> IntSet.empty
    | SNew (_, args) -> List.fold_left (fun acc a -> IntSet.union acc (method_labels_in_sterm a)) IntSet.empty args
    | SFieldAccess (e, _) -> method_labels_in_sterm e
    | SMethodInvoke (e, ml, args) ->
        List.fold_left (fun acc a -> IntSet.union acc (method_labels_in_sterm a))
            (IntSet.add ml (method_labels_in_sterm e)) args

let method_labels_in_demands (ds : demand list) =
    List.fold_left (fun acc d ->
        match d with NeedMethod (_, ml, _, _) -> IntSet.add ml acc | _ -> acc
    ) IntSet.empty ds

let rename_type (offset : int) : fj_type -> fj_type = function
    | CVar i -> CVar (i + offset)
    | ObjectType -> ObjectType
    | ClassType c -> ClassType c

let rename_demand (offset_cv : int) (offset_fl : int) (offset_ml : int)
        (d : demand) =
    let rt = rename_type offset_cv in
    match d with
    | NeedField (recv, fl, res) -> NeedField (rt recv, fl + offset_fl, rt res)
    | NeedMethod (recv, ml, params, ret) ->
        NeedMethod (rt recv, ml + offset_ml, List.map rt params, rt ret)
    | FieldCount (t, k) -> FieldCount (rt t, k)
    | Subtype (t1, t2) -> Subtype (rt t1, rt t2)

let rename_label_neq (offset_fl : int) (offset_ml : int)
        ((kind, l1, l2) : label_neq) =
    match kind with
    | LField -> (LField, l1 + offset_fl, l2 + offset_fl)
    | LMethod -> (LMethod, l1 + offset_ml, l2 + offset_ml)

let rec rename_sterm (offset_cv : int) (offset_sym : int) (offset_fl : int)
        (offset_ml : int) : proto_term -> proto_term = function
    | SFree id -> SFree (id + offset_sym)
    | SNew (typ, args) ->
        SNew (rename_type offset_cv typ,
              List.map (rename_sterm offset_cv offset_sym offset_fl offset_ml) args)
    | SFieldAccess (e, fl) ->
        SFieldAccess (rename_sterm offset_cv offset_sym offset_fl offset_ml e,
                      fl + offset_fl)
    | SMethodInvoke (e, ml, args) ->
        SMethodInvoke (rename_sterm offset_cv offset_sym offset_fl offset_ml e,
                       ml + offset_ml,
                       List.map (rename_sterm offset_cv offset_sym offset_fl offset_ml) args)

let rename_sym_map (offset_sym : int) (offset_cv : int) (m : sym_info IntMap.t) =
    IntMap.fold (fun id info acc ->
        IntMap.add (id + offset_sym) { sym_type = rename_type offset_cv info.sym_type } acc
    ) m IntMap.empty

let rename_prototerm (offset_cv : int) (offset_sym : int) (offset_fl : int)
        (offset_ml : int) (s : expr_prototerm) =
    { sterm = rename_sterm offset_cv offset_sym offset_fl offset_ml s.sterm;
      styp = rename_type offset_cv s.styp;
      sym_map = rename_sym_map offset_sym offset_cv s.sym_map;
      demands = List.map (rename_demand offset_cv offset_fl offset_ml) s.demands;
      label_neqs = List.map (rename_label_neq offset_fl offset_ml) s.label_neqs;
      next_cvar = s.next_cvar + offset_cv;
      next_sym = s.next_sym + offset_sym;
      next_field_label = s.next_field_label + offset_fl;
      next_method_label = s.next_method_label + offset_ml }

let rec merge_go (acc : expr_prototerm list) (sm : sym_info IntMap.t)
        (demands : demand list) (neqs : label_neq list)
        (ncv : int) (nsym : int) (nfl : int) (nml : int)
        : expr_prototerm list -> _ = function
    | [] -> (List.rev acc, sm, demands, neqs, ncv, nsym, nfl, nml)
    | s :: tl ->
        let s' = rename_prototerm ncv nsym nfl nml s in
        let sm' = IntMap.union (fun _ a _ -> Some a) sm s'.sym_map in
        let demands' = demands @ s'.demands in
        let neqs' = neqs @ s'.label_neqs in
        merge_go (s' :: acc) sm' demands' neqs'
            s'.next_cvar s'.next_sym s'.next_field_label s'.next_method_label tl

let merge_prototerm_contexts (prototerms : expr_prototerm list) =
    match prototerms with
    | [] -> ([], IntMap.empty, [], [], 0, 0, 0, 0)
    | first :: rest ->
        merge_go [first] first.sym_map first.demands first.label_neqs
            first.next_cvar first.next_sym first.next_field_label
            first.next_method_label rest

let field_access_variant (s : expr_prototerm) (fl : field_label)
        (nfl : field_label) (neqs : label_neq list) =
    let result_cv = s.next_cvar in
    { sterm = SFieldAccess (s.sterm, fl);
      styp = CVar result_cv;
      sym_map = s.sym_map;
      demands = NeedField (s.styp, fl, CVar result_cv) :: s.demands;
      label_neqs = neqs;
      next_cvar = result_cv + 1;
      next_sym = s.next_sym;
      next_field_label = nfl;
      next_method_label = s.next_method_label }

let try_field_access (s : expr_prototerm) =
    let existing_fls = IntSet.elements (field_labels_in_prototerm s) in
    let reuse_variants = List.map (fun fl ->
        field_access_variant s fl s.next_field_label s.label_neqs
    ) existing_fls in
    let fresh_fl = s.next_field_label in
    let fresh_neqs = List.map (fun fl -> (LField, fresh_fl, fl)) existing_fls in
    let fresh_variant =
        field_access_variant s fresh_fl (fresh_fl + 1) (fresh_neqs @ s.label_neqs) in
    reuse_variants @ [fresh_variant]

let try_new_k (args : expr_prototerm list) =
    let k = List.length args in
    let (args', sm, demands, neqs, ncv, nsym, nfl, nml) = merge_prototerm_contexts args in
    let target_cv = ncv in
    let target_type = CVar target_cv in
    let count_demand = FieldCount (target_type, k) in
    let subtype_demands = List.mapi (fun i arg ->
        let field_type_cv = CVar (target_cv + 1 + i) in
        Subtype (arg.styp, field_type_cv)
    ) args' in
    let field_demands = List.mapi (fun i _arg ->
        let fl = nfl + i in
        let field_type_cv = CVar (target_cv + 1 + i) in
        NeedField (target_type, fl, field_type_cv)
    ) args' in
    let field_neqs = List.concat_map (fun i ->
        List.filter_map (fun j ->
            if j > i then Some (LField, nfl + i, nfl + j) else None
        ) (List.init k Fun.id)
    ) (List.init k Fun.id) in
    [{ sterm = SNew (target_type, List.map (fun a -> a.sterm) args');
       styp = target_type;
       sym_map = sm;
       demands = count_demand :: subtype_demands @ field_demands @ demands;
       label_neqs = field_neqs @ neqs;
       next_cvar = target_cv + 1 + k;
       next_sym = nsym;
       next_field_label = nfl + k;
       next_method_label = nml }]

let invoke_variant (recv' : expr_prototerm) (args' : expr_prototerm list)
        (sm : sym_info IntMap.t) (demands : demand list)
        (neqs : label_neq list) (ncv : int) (nsym : int) (nfl : int)
        (ml : method_label) (nml' : method_label)
        (extra_neqs : label_neq list) =
    let n_params = List.length args' in
    let ret_cv = ncv in
    let param_cvs = List.init n_params (fun i -> CVar (ncv + 1 + i)) in
    let subtype_demands = List.map2 (fun arg pcv ->
        Subtype (arg.styp, pcv)
    ) args' param_cvs in
    { sterm = SMethodInvoke (recv'.sterm, ml,
                             List.map (fun a -> a.sterm) args');
      styp = CVar ret_cv;
      sym_map = sm;
      demands = NeedMethod (recv'.styp, ml, param_cvs, CVar ret_cv)
                :: subtype_demands @ demands;
      label_neqs = extra_neqs @ neqs;
      next_cvar = ncv + 1 + n_params;
      next_sym = nsym;
      next_field_label = nfl;
      next_method_label = nml' }

let try_invoke_k (recv : expr_prototerm) (args : expr_prototerm list) =
    let all_prototerms = recv :: args in
    let (all', sm, demands, neqs, ncv, nsym, nfl, nml) = merge_prototerm_contexts all_prototerms in
    let recv' = List.hd all' in
    let args' = List.tl all' in
    let existing_mls = IntSet.elements (
        IntSet.union
            (method_labels_in_sterm recv'.sterm)
            (List.fold_left (fun acc a ->
                IntSet.union acc (method_labels_in_sterm a.sterm)
            ) IntSet.empty args')
        |> IntSet.union (method_labels_in_demands demands)
    ) in
    let variant = invoke_variant recv' args' sm demands neqs ncv nsym nfl in
    let reuse_variants = List.map (fun ml -> variant ml nml []) existing_mls in
    let fresh_ml = nml in
    let fresh_neqs = List.map (fun ml -> (LMethod, fresh_ml, ml)) existing_mls in
    let fresh_variant = variant fresh_ml (nml + 1) fresh_neqs in
    reuse_variants @ [fresh_variant]

let rec subst_sfree (j : int) (i : int) : proto_term -> proto_term = function
    | SFree id -> SFree (if id = j then i else id)
    | SNew (t, args) -> SNew (t, List.map (subst_sfree j i) args)
    | SFieldAccess (e, fl) -> SFieldAccess (subst_sfree j i e, fl)
    | SMethodInvoke (e, ml, args) ->
        SMethodInvoke (subst_sfree j i e, ml, List.map (subst_sfree j i) args)

let subst_cvar_type (old_id : int) (new_id : int) : fj_type -> fj_type = function
    | CVar i when i = old_id -> CVar new_id
    | t -> t

let subst_cvar_demand (old_id : int) (new_id : int) (d : demand) =
    let st = subst_cvar_type old_id new_id in
    match d with
    | NeedField (recv, fl, res) -> NeedField (st recv, fl, st res)
    | NeedMethod (recv, ml, params, ret) ->
        NeedMethod (st recv, ml, List.map st params, st ret)
    | FieldCount (t, k) -> FieldCount (st t, k)
    | Subtype (t1, t2) -> Subtype (st t1, st t2)

let contract_pair (s : expr_prototerm) ((i, info_i) : int * sym_info)
        ((j, info_j) : int * sym_info) =
    if j <= i then None else
    match info_i.sym_type, info_j.sym_type with
    | CVar ci, CVar cj ->
        let sterm' = subst_sfree j i s.sterm in
        let sym_map' = IntMap.remove j s.sym_map in
        if ci = cj then Some { s with sterm = sterm'; sym_map = sym_map' } else
        let demands' = List.map (subst_cvar_demand cj ci) s.demands in
        Some { s with
               sterm = sterm';
               styp = subst_cvar_type cj ci s.styp;
               sym_map = IntMap.map (fun info ->
                   { sym_type = subst_cvar_type cj ci info.sym_type }
               ) sym_map';
               demands = demands' }
    | _ -> None

let try_contract (s : expr_prototerm) =
    let syms = IntMap.bindings s.sym_map in
    if List.length syms < 2 then [] else
    List.concat_map (fun si -> List.filter_map (contract_pair s si) syms) syms

let try_add_class (p : program_prototerm) =
    let cl = p.next_class_label in
    let base = { cl_label = cl; cl_parent = None; cl_fields = [] } in
    let obj_variant = { p with classes = base :: p.classes;
        next_class_label = cl + 1 } in
    let extend_variants = List.map (fun ce ->
        { p with classes = { base with cl_parent = Some ce.cl_label } :: p.classes;
          next_class_label = cl + 1 }
    ) p.classes in
    obj_variant :: extend_variants

let try_add_field (p : program_prototerm) =
    if p.classes = [] then [] else
    List.map (fun target ->
        let fl = p.next_field_label in
        let ft = CVar p.next_cvar in
        let updated = { target with cl_fields = target.cl_fields @ [(fl, ft)] } in
        let classes' = List.map (fun ce ->
            if ce.cl_label = target.cl_label then updated else ce
        ) p.classes in
        { p with classes = classes';
          next_field_label = fl + 1; next_cvar = p.next_cvar + 1 }
    ) p.classes

let assign_cap = 50
let materialize_cap = 20

let capped_label_mappings (cap : int)
        (options_per_fl : (field_label * field_label list) list) =
    FjConcretization.seq_product (List.map (fun (efl, opts) ->
        List.map (fun pfl -> (efl, pfl)) opts) options_per_fl)
    |> Seq.take cap
    |> List.of_seq

let rec subst_fl_sterm (old_fl : field_label) (new_fl : field_label)
        : proto_term -> proto_term = function
    | SFree id -> SFree id
    | SNew (t, args) ->
        SNew (t, List.map (subst_fl_sterm old_fl new_fl) args)
    | SFieldAccess (e, fl) ->
        SFieldAccess (subst_fl_sterm old_fl new_fl e,
                      if fl = old_fl then new_fl else fl)
    | SMethodInvoke (e, ml, args) ->
        SMethodInvoke (subst_fl_sterm old_fl new_fl e, ml,
                       List.map (subst_fl_sterm old_fl new_fl) args)

let subst_fl_demand (old_fl : field_label) (new_fl : field_label)
        : demand -> demand = function
    | NeedField (r, fl, t) -> NeedField (r, (if fl = old_fl then new_fl else fl), t)
    | d -> d

let subst_fl_neq (old_fl : field_label) (new_fl : field_label)
        ((kind, l1, l2) : label_neq) = match kind with
    | LField -> (LField, (if l1 = old_fl then new_fl else l1),
                          (if l2 = old_fl then new_fl else l2))
    | LMethod -> (kind, l1, l2)

let subst_fl_prototerm (old_fl : field_label) (new_fl : field_label)
        (s : expr_prototerm) =
    { s with sterm = subst_fl_sterm old_fl new_fl s.sterm;
             demands = List.map (subst_fl_demand old_fl new_fl) s.demands;
             label_neqs = List.map (subst_fl_neq old_fl new_fl) s.label_neqs }

let apply_fl_mapping (e : expr_prototerm)
        (mapping : (field_label * field_label) list) =
    List.fold_left (fun acc (efl, pfl) ->
        if efl = pfl then acc else subst_fl_prototerm efl pfl acc
    ) e mapping

let assign_main_to (p : program_prototerm) (e'' : expr_prototerm) =
    { p with main = Some e'';
      all_demands = p.all_demands @ e''.demands;
      all_label_neqs = p.all_label_neqs @ e''.label_neqs;
      next_cvar = e''.next_cvar;
      next_field_label = max p.next_field_label e''.next_field_label;
      next_method_label = e''.next_method_label }

let try_assign_main (p : program_prototerm) (e : expr_prototerm) =
    if p.main <> None then [] else
    let e' = rename_prototerm p.next_cvar 0 0 p.next_method_label e in
    let expr_fls = IntSet.elements (field_labels_in_prototerm e') in
    let prog_fls = List.concat_map (fun ce ->
        List.map fst ce.cl_fields) p.classes in
    if expr_fls = [] then [assign_main_to p e'] else
    let options_per_fl = List.map (fun efl ->
        (efl, prog_fls @ [efl])
    ) expr_fls in
    let mappings = capped_label_mappings assign_cap options_per_fl in
    List.map (fun mapping -> assign_main_to p (apply_fl_mapping e' mapping))
        mappings

let subst_cvar_ty (old_id : int) (t' : fj_type) : fj_type -> fj_type = function
    | CVar i when i = old_id -> t'
    | t -> t

let rec subst_cvar_ty_sterm (old_id : int) (t' : fj_type)
        : proto_term -> proto_term = function
    | SFree id -> SFree id
    | SNew (t, args) ->
        SNew (subst_cvar_ty old_id t' t,
              List.map (subst_cvar_ty_sterm old_id t') args)
    | SFieldAccess (e, fl) -> SFieldAccess (subst_cvar_ty_sterm old_id t' e, fl)
    | SMethodInvoke (e, ml, args) ->
        SMethodInvoke (subst_cvar_ty_sterm old_id t' e, ml,
                       List.map (subst_cvar_ty_sterm old_id t') args)

let subst_cvar_ty_demand (old_id : int) (t' : fj_type) (d : demand) =
    let st = subst_cvar_ty old_id t' in
    match d with
    | NeedField (recv, fl, res) -> NeedField (st recv, fl, st res)
    | NeedMethod (recv, ml, params, ret) ->
        NeedMethod (st recv, ml, List.map st params, st ret)
    | FieldCount (t, k) -> FieldCount (st t, k)
    | Subtype (t1, t2) -> Subtype (st t1, st t2)

let subst_cvar_ty_expr (old_id : int) (t' : fj_type) (e : expr_prototerm) =
    { e with
      sterm = subst_cvar_ty_sterm old_id t' e.sterm;
      styp = subst_cvar_ty old_id t' e.styp;
      sym_map = IntMap.map (fun info ->
          { sym_type = subst_cvar_ty old_id t' info.sym_type }) e.sym_map;
      demands = List.map (subst_cvar_ty_demand old_id t') e.demands }

let materialize_variant (p : program_prototerm) (target_ce : class_entry)
        (this_sym : int) (this_info : sym_info) (e' : expr_prototerm)
        (fl_map : (field_label * field_label) list) =
    let ml = p.next_method_label in
    let e'' = apply_fl_mapping e' fl_map in
    let e'' = match this_info.sym_type with
        | CVar cv ->
            subst_cvar_ty_expr cv (ClassType target_ce.cl_label) e''
        | _ -> e'' in
    let params = List.filter (fun (id, _) -> id <> this_sym)
        (IntMap.bindings e''.sym_map) in
    let me = {
        mt_class = target_ce.cl_label;
        mt_label = ml;
        mt_this_sym = this_sym;
        mt_params = List.map (fun (id, info) -> (id, info.sym_type)) params;
        mt_return = e''.styp;
        mt_body = e'';
    } in
    { p with
      methods = me :: p.methods;
      all_demands = p.all_demands @ e''.demands;
      all_label_neqs = p.all_label_neqs @ e''.label_neqs;
      next_cvar = e''.next_cvar;
      next_method_label = ml + 1;
      next_field_label = max p.next_field_label e''.next_field_label }

let materialize_for_sym (p : program_prototerm) (e' : expr_prototerm)
        (target_ce : class_entry) ((this_sym, this_info) : int * sym_info) =
    let expr_fls = IntSet.elements (field_labels_in_prototerm e') in
    let prog_fls = List.concat_map (fun ce ->
        List.map fst ce.cl_fields) p.classes in
    let fl_options = List.map (fun efl ->
        (efl, prog_fls @ [efl])
    ) expr_fls in
    let fl_mappings = capped_label_mappings materialize_cap fl_options in
    List.map (materialize_variant p target_ce this_sym this_info e') fl_mappings

let try_materialize_method (p : program_prototerm) (e : expr_prototerm) =
    if p.classes = [] then [] else
    let n_syms = IntMap.cardinal e.sym_map in
    if n_syms = 0 then [] else
    let e' = rename_prototerm p.next_cvar 0 0 0 e in
    let syms = IntMap.bindings e'.sym_map in
    List.concat_map (fun target_ce ->
        List.concat_map (materialize_for_sym p e' target_ce) syms
    ) p.classes

let sort_program = 0
let sort_expr = 1

type prototerm = tagged_prototerm
type fact = tagged_fact

let sort_count = 2
let prototerm_sort : tagged_prototerm -> int = function
    | ExprPrototerm _ -> sort_expr
    | ProgramPrototerm _ | FaultedProgram _ -> sort_program
let output_sorts = [sort_program]

type prototerm_key =
    | EK of proto_term * fj_type * demand list * label_neq list
    | PK of class_entry list * method_entry list * expr_prototerm option
    | FK of class_entry list * method_entry list * expr_prototerm option * fault
type fact_key = string

let prototerm_key : tagged_prototerm -> prototerm_key = function
    | ExprPrototerm s -> EK (s.sterm, s.styp, s.demands, s.label_neqs)
    | ProgramPrototerm p -> PK (p.classes, p.methods, p.main)
    | FaultedProgram (p, f) -> FK (p.classes, p.methods, p.main, f)
let fact_key (f : tagged_fact) = f.tf_rendered

let compare_prototerm_key : prototerm_key -> prototerm_key -> int = compare
let compare_fact_key : fact_key -> fact_key -> int = compare

let fact_depth (f : tagged_fact) = term_depth_fj f.tf_main_term
let fact_nodes (f : tagged_fact) = term_nodes_fj f.tf_main_term
let fact_unique_vars (_ : tagged_fact) = 0

let rec sterm_nodes_fj : proto_term -> int = function
    | SFree _ -> 1
    | SNew (_, args) ->
        1 + List.fold_left (fun acc a -> acc + sterm_nodes_fj a) 0 args
    | SFieldAccess (e, _) -> 1 + sterm_nodes_fj e
    | SMethodInvoke (e, _, args) ->
        1 + sterm_nodes_fj e
          + List.fold_left (fun acc a -> acc + sterm_nodes_fj a) 0 args

let prototerm_min_size : tagged_prototerm -> int = function
    | ExprPrototerm s -> sterm_nodes_fj s.sterm
    | ProgramPrototerm p | FaultedProgram (p, _) ->
        (match p.main with
         | Some e -> sterm_nodes_fj e.sterm
         | None -> 1)

let make_var_prototerm () =
    { sterm = SFree 0;
      styp = CVar 0;
      sym_map = IntMap.singleton 0 { sym_type = CVar 0 };
      demands = [];
      label_neqs = [];
      next_cvar = 1;
      next_sym = 1;
      next_field_label = 0;
      next_method_label = 0 }

let make_empty_program () =
    { classes = []; methods = []; main = None;
      all_demands = []; all_label_neqs = [];
      next_class_label = 0; next_cvar = 0;
      next_field_label = 0; next_method_label = 0 }

let make_new0_expr () =
    ExprPrototerm { sterm = SNew (CVar 0, []); styp = CVar 0;
      sym_map = IntMap.empty; demands = [FieldCount (CVar 0, 0)];
      label_neqs = []; next_cvar = 1; next_sym = 0;
      next_field_label = 0; next_method_label = 0 }

let all_seeds_ms = [
    ExprPrototerm (make_var_prototerm ());
    ExprPrototerm (FjConcretization.make_object_prototerm ());
    make_new0_expr ();
    ProgramPrototerm (make_empty_program ());
]

type seed_state = int
let initial_seeds = 0
let next_seed (_config : config) (idx : seed_state) =
    if idx >= List.length all_seeds_ms then None else
    Some (List.nth all_seeds_ms idx, idx + 1)

let satisfiability_config : FjPrototerms.config = { max_cvars = max_int }

let state_admits_assignment (st : FjConcretization.solve_state) =
    Seq.exists (FjConcretization.assignment_admissible st)
        (FjConcretization.type_assignments satisfiability_config st)

let satisfiable_program (p : program_prototerm) =
    Seq.exists state_admits_assignment (FjConcretization.solve_program p)

let demands_program_of_expr (e : expr_prototerm) =
    { classes = []; methods = []; main = None;
      all_demands = e.demands; all_label_neqs = e.label_neqs;
      next_class_label = 0; next_cvar = e.next_cvar;
      next_field_label = e.next_field_label;
      next_method_label = e.next_method_label }

let viable (s : tagged_prototerm) =
    match s with
    | ExprPrototerm e -> satisfiable_program (demands_program_of_expr e)
    | ProgramPrototerm p | FaultedProgram (p, _) -> satisfiable_program p

let filter_rule_outputs
        (((name, ins, out, suit, expand)) : tagged_prototerm Language.rule)
        : tagged_prototerm Language.rule =
    (name, ins, out, suit,
     fun (inputs : tagged_prototerm list) -> Seq.filter viable (expand inputs))

type config = FjPrototerms.config
let parse_config (kvs : (string * string) list) =
    { max_cvars =
        (match List.assoc_opt "max_cvars" kvs with
         | Some s -> (match int_of_string_opt s with Some i -> i | None -> 5)
         | None -> 5) }

let progs (ps : program_prototerm list) =
    Seq.map (fun p -> ProgramPrototerm p) (List.to_seq ps)

let exprs (es : expr_prototerm list) =
    Seq.map (fun e -> ExprPrototerm e) (List.to_seq es)

let always (_ : tagged_prototerm list) = true

let rules (_config : config) : prototerm Language.rule list =
    List.map filter_rule_outputs [
        ("add_class", [sort_program], sort_program, always,
         (function [ProgramPrototerm p] -> progs (try_add_class p) | _ -> Seq.empty));
        ("add_field", [sort_program], sort_program,
         (function [ProgramPrototerm p] -> p.classes <> [] | _ -> false),
         (function [ProgramPrototerm p] -> progs (try_add_field p) | _ -> Seq.empty));
        ("field", [sort_expr], sort_expr, always,
         (function [ExprPrototerm s] -> exprs (try_field_access s) | _ -> Seq.empty));
        ("new_1", [sort_expr], sort_expr, always,
         (function [ExprPrototerm s] -> exprs (try_new_k [s]) | _ -> Seq.empty));
        ("new_2", [sort_expr; sort_expr], sort_expr, always,
         (function [ExprPrototerm s1; ExprPrototerm s2] -> exprs (try_new_k [s1; s2]) | _ -> Seq.empty));
        ("invoke_0", [sort_expr], sort_expr, always,
         (function [ExprPrototerm r] -> exprs (try_invoke_k r []) | _ -> Seq.empty));
        ("invoke_1", [sort_expr; sort_expr], sort_expr, always,
         (function [ExprPrototerm r; ExprPrototerm a] -> exprs (try_invoke_k r [a]) | _ -> Seq.empty));
        ("contract", [sort_expr], sort_expr,
         (function [ExprPrototerm s] -> IntMap.cardinal s.sym_map >= 2 | _ -> false),
         (function [ExprPrototerm s] -> exprs (try_contract s) | _ -> Seq.empty));
        ("assign_main", [sort_program; sort_expr], sort_program,
         (function ProgramPrototerm p :: _ -> p.main = None | _ -> false),
         (function [ProgramPrototerm p; ExprPrototerm e] -> progs (try_assign_main p e) | _ -> Seq.empty));
        ("materialize_method", [sort_program; sort_expr], sort_program,
         (function ProgramPrototerm p :: _ -> p.classes <> [] | _ -> false),
         (function [ProgramPrototerm p; ExprPrototerm e] -> progs (try_materialize_method p e) | _ -> Seq.empty));
    ]

let concretize = FjIllTyped.concretize
let techniques = FjIllTyped.techniques
