open FjPrograms
open FjPrototerms

let rec all_fields_of (classes : class_entry list) (cl : int) =
    match List.find_opt (fun ce -> ce.cl_label = cl) classes with
    | None -> [] | Some ce ->
        let inherited = match ce.cl_parent with
            | None -> [] | Some p -> all_fields_of classes p in
        inherited @ ce.cl_fields

let rec is_subtype_cl (classes : class_entry list) (sub : int) (sup : int) =
    if sub = sup then true else
    match List.find_opt (fun ce -> ce.cl_label = sub) classes with
        | None -> false
        | Some ce -> (match ce.cl_parent with
            | None -> false | Some p -> is_subtype_cl classes p sup)

let is_subtype_concrete (classes : class_entry list)
        (sub : concrete_type) (sup : concrete_type) =
    match sub, sup with
    | _, ConcreteObject -> true
    | ConcreteObject, ConcreteClass _ -> false
    | ConcreteClass a, ConcreteClass b -> is_subtype_cl classes a b

let make_object_prototerm () =
    { sterm = SNew (ObjectType, []);
      styp = ObjectType;
      sym_map = IntMap.empty;
      demands = [];
      label_neqs = [];
      next_cvar = 0;
      next_sym = 0;
      next_field_label = 0;
      next_method_label = 0 }

let rec seq_product : 'a list list -> 'a list Seq.t = function
    | [] -> Seq.return []
    | options :: rest ->
        let tail = seq_product rest in
        Seq.concat_map (fun x -> Seq.map (fun r -> x :: r) tail)
            (List.to_seq options)

let cvars_in_type_set : fj_type -> IntSet.t = function
    | CVar i -> IntSet.singleton i
    | ObjectType | ClassType _ -> IntSet.empty

let rec cvars_in_sterm : proto_term -> IntSet.t = function
    | SFree _ -> IntSet.empty
    | SNew (t, args) ->
        List.fold_left (fun acc a -> IntSet.union acc (cvars_in_sterm a))
            (cvars_in_type_set t) args
    | SFieldAccess (e, _) -> cvars_in_sterm e
    | SMethodInvoke (e, _, args) ->
        List.fold_left (fun acc a -> IntSet.union acc (cvars_in_sterm a))
            (cvars_in_sterm e) args

let cvars_in_demand : demand -> IntSet.t = function
    | NeedField (r, _, t) -> IntSet.union (cvars_in_type_set r) (cvars_in_type_set t)
    | NeedMethod (r, _, ps, t) ->
        List.fold_left (fun a p -> IntSet.union a (cvars_in_type_set p))
            (IntSet.union (cvars_in_type_set r) (cvars_in_type_set t)) ps
    | FieldCount (t, _) -> cvars_in_type_set t
    | Subtype (a, b) -> IntSet.union (cvars_in_type_set a) (cvars_in_type_set b)

let cvars_in_expr (e : expr_prototerm) =
    IntSet.union (cvars_in_sterm e.sterm)
        (IntSet.union (cvars_in_type_set e.styp)
            (IntMap.fold (fun _ info a -> IntSet.union a (cvars_in_type_set info.sym_type))
                e.sym_map IntSet.empty))

let cvars_in_program (p : program_prototerm) =
    let from_classes = List.fold_left (fun acc ce ->
        List.fold_left (fun a (_, ft) -> IntSet.union a (cvars_in_type_set ft)) acc ce.cl_fields
    ) IntSet.empty p.classes in
    let from_main = match p.main with None -> IntSet.empty | Some e -> cvars_in_expr e in
    let from_methods = List.fold_left (fun acc me ->
        IntSet.union acc (IntSet.union (cvars_in_expr me.mt_body)
            (IntSet.union (cvars_in_type_set me.mt_return)
                (List.fold_left (fun a (_, t) -> IntSet.union a (cvars_in_type_set t))
                    IntSet.empty me.mt_params)))
    ) IntSet.empty p.methods in
    let from_demands = List.fold_left (fun a d -> IntSet.union a (cvars_in_demand d))
        IntSet.empty p.all_demands in
    IntSet.union from_classes (IntSet.union from_main
        (IntSet.union from_methods from_demands))

let resolve_type (assignment : (int * concrete_type) list)
        : fj_type -> concrete_type = function
    | ObjectType -> ConcreteObject
    | ClassType c -> ConcreteClass c
    | CVar i -> (match List.assoc_opt i assignment with
        | Some ct -> ct | None -> ConcreteObject)

let rec method_satisfies (classes : class_entry list)
        (methods : method_entry list)
        (assignment : (int * concrete_type) list) (param_types : fj_type list)
        (ret : fj_type) (prog_ml : method_label) (c : int) =
    match List.find_opt (fun me ->
        me.mt_class = c && me.mt_label = prog_ml) methods with
    | Some me ->
        List.length param_types = List.length me.mt_params &&
        is_subtype_concrete classes
            (resolve_type assignment me.mt_return)
            (resolve_type assignment ret) &&
        List.for_all2 (fun pt (_, mpt) ->
            resolve_type assignment pt = resolve_type assignment mpt
        ) param_types me.mt_params
    | None ->
        (match List.find_opt (fun ce -> ce.cl_label = c) classes with
        | Some ce -> (match ce.cl_parent with
            | Some parent ->
                method_satisfies classes methods assignment param_types ret
                    prog_ml parent
            | None -> false)
        | None -> false)

let check_demand (classes : class_entry list) (methods : method_entry list)
        (assignment : (int * concrete_type) list)
        (fl_map : (int * field_label) list) (ml_map : (int * method_label) list)
        (d : demand) =
    match d with
    | FieldCount (t, k) ->
        (match resolve_type assignment t with
        | ConcreteObject -> k = 0
        | ConcreteClass cl -> List.length (all_fields_of classes cl) = k)
    | Subtype (t1, t2) ->
        is_subtype_concrete classes (resolve_type assignment t1)
            (resolve_type assignment t2)
    | NeedField (recv, fl, res) ->
        (match resolve_type assignment recv with
        | ConcreteObject -> false
        | ConcreteClass cl ->
            let fields = all_fields_of classes cl in
            (match List.assoc_opt fl fl_map with
            | None -> false
            | Some prog_fl ->
                (match List.assoc_opt prog_fl fields with
                | None -> false
                | Some ft ->
                    resolve_type assignment res = resolve_type assignment ft)))
    | NeedMethod (recv, ml, param_types, ret) ->
        (match resolve_type assignment recv with
        | ConcreteObject -> false
        | ConcreteClass cl ->
            (match List.assoc_opt ml ml_map with
            | None -> false
            | Some prog_ml ->
                method_satisfies classes methods assignment param_types ret
                    prog_ml cl))

let check_demands (classes : class_entry list) (methods : method_entry list)
        (assignment : (int * concrete_type) list)
        (fl_map : (int * field_label) list) (ml_map : (int * method_label) list)
        (demands : demand list) =
    List.for_all (check_demand classes methods assignment fl_map ml_map) demands

let check_label_neq (fl_map : (int * field_label) list)
        (((kind, l1, l2)) : label_neq) =
    match kind with
    | LField ->
        let r1 = (match List.assoc_opt l1 fl_map with Some v -> v | None -> l1) in
        let r2 = (match List.assoc_opt l2 fl_map with Some v -> v | None -> l2) in
        r1 <> r2
    | LMethod -> true

let check_label_neqs (fl_map : (int * field_label) list) (neqs : label_neq list) =
    List.for_all (check_label_neq fl_map) neqs

let remap_fl (fl_map : (int * field_label) list) (fl : field_label) =
    match List.assoc_opt fl fl_map with Some v -> v | None -> fl

let remap_ml (ml_map : (int * method_label) list) (ml : method_label) =
    match List.assoc_opt ml ml_map with Some v -> v | None -> ml

let rec resolve_sterm_mapped (assignment : (int * concrete_type) list)
        (fl_map : (int * field_label) list) (ml_map : (int * method_label) list)
        : proto_term -> term = function
    | SFree id -> Var id
    | SNew (typ, args) ->
        let cls = match resolve_type assignment typ with
            | ConcreteObject -> -1 | ConcreteClass cl -> cl in
        New (cls, List.map (resolve_sterm_mapped assignment fl_map ml_map) args)
    | SFieldAccess (e, fl) ->
        FieldAccess (resolve_sterm_mapped assignment fl_map ml_map e,
                     remap_fl fl_map fl)
    | SMethodInvoke (e, ml, args) ->
        MethodInvoke (resolve_sterm_mapped assignment fl_map ml_map e,
                      remap_ml ml_map ml,
                      List.map (resolve_sterm_mapped assignment fl_map ml_map) args)

let concrete_class_entry_of (assignment : (int * concrete_type) list)
        (ce : class_entry) =
    { cc_label = ce.cl_label;
      cc_parent = (match ce.cl_parent with None -> -1 | Some p -> p);
      cc_own_fields = List.map (fun (fl, ft) ->
          (fl, resolve_type assignment ft)) ce.cl_fields }

let concrete_method_entry_of (assignment : (int * concrete_type) list)
        (fl_map : (int * field_label) list) (ml_map : (int * method_label) list)
        (me : method_entry) =
    { cm_class = me.mt_class;
      cm_label = me.mt_label;
      cm_this_sym = me.mt_this_sym;
      cm_params = List.map (fun (sid, pt) ->
          (sid, resolve_type assignment pt)) me.mt_params;
      cm_return = resolve_type assignment me.mt_return;
      cm_body = resolve_sterm_mapped assignment fl_map ml_map me.mt_body.sterm }

let render_method_decl (assignment : (int * concrete_type) list)
        (fl_map : (int * field_label) list) (ml_map : (int * method_label) list)
        (buf : Buffer.t) (cl : int) (me : method_entry) =
    if me.mt_class = cl then begin
        let ret_s = string_of_concrete_type
            (resolve_type assignment me.mt_return) in
        let params_s = String.concat ", " (List.map (fun (sid, pt) ->
            string_of_concrete_type (resolve_type assignment pt) ^
            " x" ^ string_of_int sid
        ) me.mt_params) in
        let body_term =
            resolve_sterm_mapped assignment fl_map ml_map me.mt_body.sterm in
        Buffer.add_string buf ("  " ^ ret_s ^ " " ^
            ml_name me.mt_label ^ "(" ^ params_s ^
            ") { return " ^ string_of_term body_term ^ "; }\n")
    end

let render_class_decl (p : program_prototerm)
        (assignment : (int * concrete_type) list)
        (fl_map : (int * field_label) list) (ml_map : (int * method_label) list)
        (buf : Buffer.t) (ce : class_entry) =
    let parent = match ce.cl_parent with
        | None -> "Object" | Some pp -> cl_name pp in
    Buffer.add_string buf ("class " ^ cl_name ce.cl_label ^
        " extends " ^ parent ^ " {");
    List.iter (fun (fl, ft) ->
        let ft_s = string_of_concrete_type (resolve_type assignment ft) in
        Buffer.add_string buf (" " ^ ft_s ^ " " ^ fl_name fl ^ ";")
    ) (all_fields_of p.classes ce.cl_label);
    Buffer.add_string buf " }\n";
    List.iter (render_method_decl assignment fl_map ml_map buf ce.cl_label)
        p.methods

let build_tagged_fact (p : program_prototerm) (e : expr_prototerm)
        (assignment : (int * concrete_type) list)
        (fl_map : (int * field_label) list) (ml_map : (int * method_label) list) =
    let classes = List.map (concrete_class_entry_of assignment) p.classes in
    let methods =
        List.map (concrete_method_entry_of assignment fl_map ml_map) p.methods in
    let main_term = resolve_sterm_mapped assignment fl_map ml_map e.sterm in
    let main_type = resolve_type assignment e.styp in
    let bindings = List.map (fun (sid, info) ->
        (sid, resolve_type assignment info.sym_type)
    ) (IntMap.bindings e.sym_map) in
    let buf = Buffer.create 256 in
    List.iter (render_class_decl p assignment fl_map ml_map buf)
        (List.rev p.classes);
    Buffer.add_string buf ("main: " ^ string_of_term main_term ^
        " : " ^ string_of_concrete_type main_type);
    { tf_classes = classes;
      tf_methods = methods;
      tf_main_term = main_term;
      tf_main_type = main_type;
      tf_bindings = bindings;
      tf_rendered = Buffer.contents buf }

let solve_default_ty = ObjectType

let rec sderef_seen (subst : (int * fj_type) list) (seen : int list)
        : fj_type -> fj_type = function
    | CVar i when not (List.mem i seen) ->
        (match List.assoc_opt i subst with
         | Some t' -> sderef_seen subst (i :: seen) t' | None -> CVar i)
    | t -> t

let sderef (subst : (int * fj_type) list) (t : fj_type) =
    sderef_seen subst [] t

let ground (subst : (int * fj_type) list) (t : fj_type) =
    match sderef subst t with
    | CVar _ -> solve_default_ty
    | t -> t

let to_concrete : fj_type -> concrete_type = function
    | ObjectType -> ConcreteObject
    | ClassType c -> ConcreteClass c
    | CVar _ -> ConcreteObject

type solve_state = {
    sp     : program_prototerm;
    subst  : (int * fj_type) list;
    sfl    : (int * field_label) list;
    sml    : (int * method_label) list;
    sunit  : int;
    sctors : (int * (field_label * int) list) list;
}

let bind_tv (st : solve_state) (i : int) (t : fj_type) =
    { st with subst = (i, t) :: st.subst }

let bind_if_free (st : solve_state) (ty : fj_type) =
    match sderef st.subst ty with
    | CVar i -> bind_tv st i solve_default_ty
    | _ -> st

let mint_class_parent (parent : int option) (st : solve_state) =
    let label = st.sp.next_class_label in
    let ce = { cl_label = label; cl_parent = parent; cl_fields = [] } in
    (label, { st with sp = { st.sp with
        classes = st.sp.classes @ [ce];
        next_class_label = label + 1 } })

let mint_class (st : solve_state) = mint_class_parent None st

let alloc_fl (st : solve_state) (fl_abstract : field_label) =
    match List.assoc_opt fl_abstract st.sfl with
    | Some fl -> (fl, st)
    | None ->
        let fl = st.sp.next_field_label in
        (fl, { st with sp = { st.sp with next_field_label = fl + 1 };
                       sfl = (fl_abstract, fl) :: st.sfl })

let ensure_field (st : solve_state) (c : int) (fl : field_label) (fty : fj_type) =
    let present = List.exists (fun ce ->
        ce.cl_label = c && List.mem_assoc fl ce.cl_fields) st.sp.classes in
    if present then st else
    { st with sp = { st.sp with classes = List.map (fun ce ->
        if ce.cl_label <> c then ce else
        { ce with cl_fields = ce.cl_fields @ [(fl, fty)] }) st.sp.classes } }

let alloc_ml (st : solve_state) (ml_abstract : method_label) =
    match List.assoc_opt ml_abstract st.sml with
    | Some ml -> (ml, st)
    | None ->
        let ml = st.sp.next_method_label in
        (ml, { st with sp = { st.sp with next_method_label = ml + 1 };
                       sml = (ml_abstract, ml) :: st.sml })

let rec trivial_term (st : solve_state) ?(fuel : int = 16) (ty : fj_type) =
    match ty with
    | ClassType c when fuel > 0 ->
        SNew (ty, List.map (fun (_, ft) -> trivial_term st ~fuel:(fuel - 1) ft)
                    (all_fields_of st.sp.classes c))
    | ObjectType when st.sunit >= 0 ->
        SNew (ClassType st.sunit, [])
    | _ -> SNew (ObjectType, [])

let trivial_body (st : solve_state) (ty : fj_type) : expr_prototerm =
    { sterm = trivial_term st ty; styp = ty; sym_map = IntMap.empty;
      demands = []; label_neqs = [];
      next_cvar = 0; next_sym = 0; next_field_label = 0; next_method_label = 0 }

let ensure_method (st : solve_state) (c : int) (ml : method_label)
        (param_tys : fj_type list) (ret_t : fj_type) =
    let present = List.exists (fun me ->
        me.mt_class = c && me.mt_label = ml) st.sp.methods in
    if present then st else
    let me = { mt_class = c; mt_label = ml; mt_this_sym = 0;
               mt_params = List.mapi (fun i pt -> (i + 1, pt)) param_tys;
               mt_return = ret_t; mt_body = trivial_body st ret_t } in
    { st with sp = { st.sp with methods = me :: st.sp.methods } }

let unify_ty (st : solve_state) (a : fj_type) (b : fj_type) : solve_state Seq.t =
    match sderef st.subst a, sderef st.subst b with
    | CVar i, CVar j when i = j -> Seq.return st
    | CVar i, t | t, CVar i -> Seq.return (bind_tv st i t)
    | t1, t2 -> if t1 = t2 then Seq.return st else Seq.empty

let mint_ctor (st : solve_state) (i : int)
        (ctor_fields : (field_label * int) list) =
    let (st, fields_rev) =
        List.fold_left (fun (st, acc) (fa, cv) ->
            let (fl, st) = alloc_fl st fa in
            let st = if acc = [] then bind_if_free st (CVar cv) else st in
            (st, (fl, sderef st.subst (CVar cv)) :: acc))
            (st, []) ctor_fields in
    match List.rev fields_rev with
    | first :: rest ->
        let (pc, st) = mint_class st in
        let st = ensure_field st pc (fst first) (snd first) in
        let (c, st) = mint_class_parent (Some pc) st in
        let st = List.fold_left (fun st (fl, ty) -> ensure_field st c fl ty) st rest in
        bind_tv st i (ClassType c)
    | [] ->
        let (c, st) = mint_class st in
        bind_tv st i (ClassType c)

let rec solve_field (st : solve_state) (recv : fj_type) (fa : field_label)
        (res : fj_type) : solve_state Seq.t =
    match sderef st.subst recv with
    | ClassType c ->
        let (fl, st) = alloc_fl st fa in
        (match List.assoc_opt fl (all_fields_of st.sp.classes c) with
         | Some ft -> unify_ty st ft res
         | None ->
             let st = bind_if_free st res in
             Seq.return (ensure_field st c fl (sderef st.subst res)))
    | CVar i ->
        (match List.assoc_opt i st.sctors with
         | Some ctor_fields -> solve_field (mint_ctor st i ctor_fields) recv fa res
         | None ->
             let st = bind_if_free st res in
             let (fl, st) = alloc_fl st fa in
             let fty = sderef st.subst res in
             let (pc, st) = mint_class st in
             let st = ensure_field st pc fl fty in
             let (c, st) = mint_class_parent (Some pc) st in
             Seq.return (bind_tv st i (ClassType c)))
    | ObjectType -> Seq.empty

let finish_method (freeze_params : bool) (ma : method_label)
        (param_types : fj_type list) (ret : fj_type)
        (st : solve_state) (c : int) =
    let (ml, st) = alloc_ml st ma in
    let st = bind_if_free st ret in
    let st =
        if freeze_params then List.fold_left bind_if_free st param_types else
        st in
    let ret_t = sderef st.subst ret in
    let ptys = List.map (sderef st.subst) param_types in
    Seq.return (ensure_method st c ml ptys ret_t)

let rec solve_method ?(freeze_params : bool = true) (st : solve_state)
        (recv : fj_type) (ma : method_label) (param_types : fj_type list)
        (ret : fj_type) : solve_state Seq.t =
    let finish = finish_method freeze_params ma param_types ret in
    match sderef st.subst recv with
    | ClassType c -> finish st c
    | CVar i ->
        (match List.assoc_opt i st.sctors with
         | Some ctor_fields ->
             solve_method ~freeze_params (mint_ctor st i ctor_fields)
                 recv ma param_types ret
         | None ->
             let (pc, st) = mint_class st in
             let st = finish st pc in
             (match st () with
              | Seq.Nil -> Seq.empty
              | Seq.Cons (st, _) ->
                  let (c, st) = mint_class_parent (Some pc) st in
                  Seq.return (bind_tv st i (ClassType c))))
    | ObjectType -> Seq.empty

let is_subtype_ty (sp : program_prototerm) (a : fj_type) (b : fj_type) =
    is_subtype_concrete sp.classes (to_concrete a) (to_concrete b)

let parent_ty (st : solve_state) (c : int) =
    match List.find_opt (fun ce -> ce.cl_label = c) st.sp.classes with
    | Some { cl_parent = Some p; _ } -> ClassType p
    | _ -> ObjectType

let solve_subtype (st : solve_state) (a : fj_type) (b : fj_type)
        : solve_state Seq.t =
    match sderef st.subst a, sderef st.subst b with
    | CVar i, CVar j when i = j -> Seq.return st
    | CVar i, CVar j ->
        let (pc, st) = mint_class st in
        let (c, st) = mint_class_parent (Some pc) st in
        Seq.return (bind_tv (bind_tv st j (ClassType pc)) i (ClassType c))
    | CVar i, ObjectType ->
        let (c, st) = mint_class st in
        Seq.return (bind_tv st i (ClassType c))
    | CVar i, ClassType cs ->
        let (c, st) = mint_class_parent (Some cs) st in
        Seq.return (bind_tv st i (ClassType c))
    | ObjectType, CVar i -> Seq.return (bind_tv st i ObjectType)
    | ClassType cs, CVar i -> Seq.return (bind_tv st i (parent_ty st cs))
    | da, db -> if is_subtype_ty st.sp da db then Seq.return st else Seq.empty

let rec keep_last_fields : (field_label * int) list -> (field_label * int) list
        = function
    | [] -> []
    | (fl, cv) :: rest ->
        if List.mem_assoc fl rest then keep_last_fields rest else
        (fl, cv) :: keep_last_fields rest

let ctor_fields_for (p : program_prototerm) (t : int) =
    let nfs = List.filter_map (function
        | NeedField (CVar r, fl, CVar cv) when r = t -> Some (fl, cv)
        | _ -> None) p.all_demands in
    match keep_last_fields nfs with
    | [] -> None
    | fs -> Some (t, fs)

let ctor_fields_of (p : program_prototerm) =
    List.filter_map (function
        | FieldCount (CVar t, k) when k > 0 -> Some t
        | _ -> None) p.all_demands
    |> List.filter_map (ctor_fields_for p)

let solve_member_demand (freeze_params : bool) (states : solve_state Seq.t)
        (d : demand) =
    match d with
    | NeedField (r, fa, res) ->
        Seq.concat_map (fun st -> solve_field st r fa res) states
    | NeedMethod (r, ma, args, ret) ->
        Seq.concat_map (fun st -> solve_method ~freeze_params st r ma args ret)
            states
    | _ -> states

let solve_subtype_demand (states : solve_state Seq.t) (d : demand) =
    match d with
    | Subtype (a, b) -> Seq.concat_map (fun st -> solve_subtype st a b) states
    | _ -> states

let solve_program ?(freeze_params : bool = true) (p : program_prototerm)
        : solve_state Seq.t =
    let (p, sunit) =
        let c = p.next_class_label in
        ({ p with
           classes = p.classes @ [{ cl_label = c; cl_parent = None; cl_fields = [] }];
           next_class_label = c + 1 }, c) in
    let st0 = { sp = p; subst = []; sfl = []; sml = [];
                sunit; sctors = ctor_fields_of p } in
    let after_members =
        List.fold_left (solve_member_demand freeze_params)
            (Seq.return st0) p.all_demands in
    List.fold_left solve_subtype_demand after_members p.all_demands

let solve_assignment_cap = 64

let available_types (sp : program_prototerm) =
    ObjectType :: List.map (fun ce -> ClassType ce.cl_label) sp.classes

let type_assignments (config : config) (st : solve_state)
        : (int * concrete_type) list Seq.t =
    let all_cvars = IntSet.elements (cvars_in_program st.sp) in
    let free = List.filter (fun i ->
        match sderef st.subst (CVar i) with CVar j -> j = i | _ -> false) all_cvars in
    if List.length free > config.max_cvars then Seq.empty else
    let opts = available_types st.sp in
    let options = List.map (fun i -> List.map (fun t -> (i, t)) opts) free in
    seq_product options
    |> Seq.take solve_assignment_cap
    |> Seq.map (fun free_assign ->
        let combined = st.subst @ free_assign in
        List.map (fun i -> (i, to_concrete (ground combined (CVar i)))) all_cvars)

let assignment_admissible (st : solve_state)
        (assignment : (int * concrete_type) list) =
    check_demands st.sp.classes st.sp.methods assignment
        st.sfl st.sml st.sp.all_demands
    && check_label_neqs st.sfl st.sp.all_label_neqs

let fact_of_assignment (e : expr_prototerm) (st : solve_state)
        (assignment : (int * concrete_type) list) =
    build_tagged_fact st.sp e assignment st.sfl st.sml

let solved_state_facts (config : config) (e : expr_prototerm)
        (st : solve_state) =
    type_assignments config st
    |> Seq.filter (assignment_admissible st)
    |> Seq.map (fact_of_assignment e st)

let instantiate_program_solved (config : config) (p : program_prototerm)
        : tagged_fact Seq.t =
    match p.main with
    | None -> Seq.empty
    | Some e -> Seq.concat_map (solved_state_facts config e) (solve_program p)

let concretize ~search_budget:(_ : int option) (config : config)
        (s : tagged_prototerm) =
    match s with
    | ProgramPrototerm p -> instantiate_program_solved config p
    | ExprPrototerm _ | FaultedProgram _ -> Seq.empty
