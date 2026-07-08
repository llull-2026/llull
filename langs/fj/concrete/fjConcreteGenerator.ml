open FjPrograms
open FjPrototerms
include FjConcretePrototerms

type config = FjConcretePrototerms.config

let int_kv kvs k default =
    match List.assoc_opt k kvs with
    | Some s -> (match int_of_string_opt s with Some v -> v | None -> default)
    | None -> default

let parse_config kvs =
    { max_ctx = int_kv kvs "max_ctx" 1;
      max_classes = int_kv kvs "max_classes" 3;
      max_methods = int_kv kvs "max_methods" 3 }

type prototerm_key =
    | PK of class_entry list * concrete_method list * (term * fj_type) option
    | EK of class_entry list * concrete_method list * term * fj_type * fj_type list

let prototerm_key = function
    | Prog p -> PK (p.cp_classes, p.cp_methods, p.cp_main_opt)
    | Expr e -> EK (e.ce_snapshot, e.ce_methods, e.ce_term, e.ce_typ, e.ce_sctx)

type fact_key = string
let fact_key (f : tagged_fact) = f.tf_rendered
let compare_prototerm_key = compare
let compare_fact_key = compare

let sort_program = 0
let sort_expr = 1

let sort_count = 2

let prototerm_sort = function
    | Prog _ -> sort_program
    | Expr _ -> sort_expr

let output_sorts = [sort_program]

type prototerm = FjConcretePrototerms.prototerm
type fact = FjPrograms.tagged_fact

type seed_state = int
let initial_seeds = 0
let next_seed _config = function
    | 0 -> Some (Prog { cp_classes = []; cp_methods = []; cp_main_opt = None }, 1)
    | _ -> None

let basis_for (cls : class_entry list) =
    ObjectType :: List.map (fun ce -> ClassType ce.cl_label) cls

let enumerate_ctxs base_types max_len =
    let by_len = Array.make (max_len + 1) [] in
    by_len.(0) <- [[]];
    for k = 1 to max_len do
        by_len.(k) <-
            List.concat_map (fun ctx ->
                List.map (fun t -> t :: ctx) base_types
            ) by_len.(k - 1)
    done;
    Array.fold_left (fun acc xs -> acc @ xs) [] by_len

let class_index_of = function
    | ObjectType -> -1
    | ClassType i -> i
    | CVar _ -> assert false

let rec ancestors cls c =
    match List.find_opt (fun ce -> ce.cl_label = c) cls with
    | None -> [c]
    | Some ce ->
        c :: (match ce.cl_parent with None -> [] | Some p -> ancestors cls p)

let try_add_class ~max_classes p =
    if p.cp_main_opt <> None then [] else
    if List.length p.cp_classes >= max_classes then [] else
    let new_label =
        1 + List.fold_left (fun m ce -> max m ce.cl_label) (-1) p.cp_classes in
    let base = { cl_label = new_label; cl_parent = None; cl_fields = [] } in
    let obj_variant =
        { p with cp_classes = base :: p.cp_classes } in
    let extend_variants = List.map (fun ce ->
        { p with cp_classes =
            { base with cl_parent = Some ce.cl_label } :: p.cp_classes }
    ) p.cp_classes in
    obj_variant :: extend_variants

let try_add_field p =
    if p.cp_main_opt <> None then [] else
    if p.cp_classes = [] then [] else
    if p.cp_methods <> [] then [] else
    let basis = basis_for p.cp_classes in
    List.concat_map (fun target ->
        let next_fl =
            1 + List.fold_left (fun m (fl, _) -> max m fl) (-1) target.cl_fields in
        List.map (fun ft ->
            let updated =
                { target with cl_fields = target.cl_fields @ [(next_fl, ft)] } in
            let classes' = List.map (fun ce ->
                if ce.cl_label = target.cl_label then updated else ce
            ) p.cp_classes in
            { p with cp_classes = classes' }
        ) basis
    ) p.cp_classes

let method_variant_at ~next_ml p e i t =
    match t with
    | ClassType c ->
        let params =
            List.filter (fun (j, _) -> j <> i)
                (List.mapi (fun j tj -> (j, tj)) e.ce_sctx) in
        [{ p with cp_methods =
            { me_class = c; me_label = next_ml; me_this = i;
              me_params = params; me_ret = e.ce_typ; me_body = e.ce_term }
            :: p.cp_methods }]
    | ObjectType | CVar _ -> []

let try_add_method ~max_methods p e =
    if p.cp_main_opt <> None then [] else
    if p.cp_classes = [] then [] else
    if List.length p.cp_methods >= max_methods then [] else
    if p.cp_classes <> e.ce_snapshot || p.cp_methods <> e.ce_methods then [] else
    let next_ml =
        1 + List.fold_left (fun m me -> max m me.me_label) (-1) p.cp_methods in
    List.concat (List.mapi (method_variant_at ~next_ml p e) e.ce_sctx)

let var_expr p ctx i t =
    { ce_snapshot = p.cp_classes;
      ce_methods = p.cp_methods;
      ce_term = Var i;
      ce_typ = t;
      ce_sctx = ctx }

let try_expr_var ~max_ctx p =
    if p.cp_main_opt <> None then [] else
    let basis = basis_for p.cp_classes in
    let ctxs = enumerate_ctxs basis max_ctx in
    List.concat_map (fun ctx -> List.mapi (var_expr p ctx) ctx) ctxs

let new0_expr p ctx typ =
    { ce_snapshot = p.cp_classes;
      ce_methods = p.cp_methods;
      ce_term = New (class_index_of typ, []);
      ce_typ = typ;
      ce_sctx = ctx }

let try_expr_new0 ~max_ctx p =
    if p.cp_main_opt <> None then [] else
    let basis = basis_for p.cp_classes in
    let ctxs = enumerate_ctxs basis max_ctx in
    let zero_field_classes =
        ObjectType ::
        (List.filter_map (fun ce ->
            let fields = FjConcretization.all_fields_of p.cp_classes ce.cl_label in
            if fields = [] then Some (ClassType ce.cl_label) else None
        ) p.cp_classes)
    in
    List.concat_map (fun ctx ->
        List.map (new0_expr p ctx) zero_field_classes
    ) ctxs

let try_field e =
    match e.ce_typ with
    | ObjectType | CVar _ -> []
    | ClassType c ->
        (match List.find_opt (fun ce -> ce.cl_label = c) e.ce_snapshot with
         | None -> []
         | Some _ ->
             let own_and_inherited =
                 FjConcretization.all_fields_of e.ce_snapshot c in
             List.map (fun (fl, ft) ->
                 { e with
                   ce_term = FieldAccess (e.ce_term, fl);
                   ce_typ = ft }
             ) own_and_inherited)

let class_matches_args (cls : class_entry list) arg_types : int list =
    List.filter_map (fun ce ->
        let fields = FjConcretization.all_fields_of cls ce.cl_label in
        if List.length fields <> List.length arg_types then None else
        let matches = List.for_all2 (fun (_, ft) at -> ft = at) fields arg_types in
        if matches then Some ce.cl_label else None
    ) cls

let try_new_k (args : concrete_expr list) =
    match args with
    | [] -> []
    | first :: _ ->
        if not (List.for_all (fun e ->
                e.ce_snapshot = first.ce_snapshot
                && e.ce_methods = first.ce_methods
                && e.ce_sctx = first.ce_sctx) args)
        then [] else
        let arg_types = List.map (fun e -> e.ce_typ) args in
        let matching = class_matches_args first.ce_snapshot arg_types in
        List.map (fun cid ->
            { first with
              ce_term = New (cid, List.map (fun e -> e.ce_term) args);
              ce_typ = ClassType cid }
        ) matching

let try_invoke_k recv (args : concrete_expr list) =
    if not (List.for_all (fun e ->
            e.ce_snapshot = recv.ce_snapshot
            && e.ce_methods = recv.ce_methods
            && e.ce_sctx = recv.ce_sctx) args)
    then [] else
    match recv.ce_typ with
    | ObjectType | CVar _ -> []
    | ClassType c ->
        let anc = ancestors recv.ce_snapshot c in
        let arg_types = List.map (fun e -> e.ce_typ) args in
        List.filter_map (fun me ->
            if not (List.mem me.me_class anc
                    && List.map snd me.me_params = arg_types) then None else
            Some { recv with
                   ce_term = MethodInvoke (recv.ce_term, me.me_label,
                                  List.map (fun e -> e.ce_term) args);
                   ce_typ = me.me_ret }
        ) recv.ce_methods

let try_assign_main p e =
    if p.cp_main_opt <> None then [] else
    if e.ce_sctx <> [] then [] else
    if p.cp_classes <> e.ce_snapshot || p.cp_methods <> e.ce_methods then [] else
    [{ p with cp_main_opt = Some (e.ce_term, e.ce_typ) }]

let progs ps = Seq.map (fun p -> Prog p) (List.to_seq ps)
let exprs es = Seq.map (fun e -> Expr e) (List.to_seq es)
let always _ = true
let growing = function Prog p :: _ -> p.cp_main_opt = None | _ -> false

let rules (config : config) : prototerm Language.rule list =
    [
        ("add_class", [sort_program], sort_program, growing,
         (function
            | [Prog p] -> progs (try_add_class ~max_classes:config.max_classes p)
            | _ -> Seq.empty));
        ("add_field", [sort_program], sort_program,
         (function
            | Prog p :: _ ->
                p.cp_main_opt = None && p.cp_classes <> [] && p.cp_methods = []
            | _ -> false),
         (function
            | [Prog p] -> progs (try_add_field p)
            | _ -> Seq.empty));
        ("add_method", [sort_program; sort_expr], sort_program, growing,
         (function
            | [Prog p; Expr e] ->
                progs (try_add_method ~max_methods:config.max_methods p e)
            | _ -> Seq.empty));
        ("expr_var", [sort_program], sort_expr, growing,
         (function
            | [Prog p] -> exprs (try_expr_var ~max_ctx:config.max_ctx p)
            | _ -> Seq.empty));
        ("expr_new0", [sort_program], sort_expr, growing,
         (function
            | [Prog p] -> exprs (try_expr_new0 ~max_ctx:config.max_ctx p)
            | _ -> Seq.empty));
        ("field", [sort_expr], sort_expr, always,
         (function
            | [Expr e] -> exprs (try_field e)
            | _ -> Seq.empty));
        ("new_1", [sort_expr], sort_expr, always,
         (function
            | [Expr a] -> exprs (try_new_k [a])
            | _ -> Seq.empty));
        ("new_2", [sort_expr; sort_expr], sort_expr, always,
         (function
            | [Expr a; Expr b] -> exprs (try_new_k [a; b])
            | _ -> Seq.empty));
        ("invoke_0", [sort_expr], sort_expr, always,
         (function
            | [Expr a] -> exprs (try_invoke_k a [])
            | _ -> Seq.empty));
        ("invoke_1", [sort_expr; sort_expr], sort_expr, always,
         (function
            | [Expr a; Expr b] -> exprs (try_invoke_k a [b])
            | _ -> Seq.empty));
        ("assign_main", [sort_program; sort_expr], sort_program, growing,
         (function
            | [Prog p; Expr e] -> progs (try_assign_main p e)
            | _ -> Seq.empty));
    ]

let fact_depth (f : tagged_fact) = term_depth_fj f.tf_main_term
let fact_nodes (f : tagged_fact) = term_nodes_fj f.tf_main_term
let fact_unique_vars _ = 0

let prototerm_min_size = function
    | Prog p ->
        (match p.cp_main_opt with
         | Some (t, _) -> term_nodes_fj t
         | None -> 1)
    | Expr e -> term_nodes_fj e.ce_term

let viable (_ : config) (_ : prototerm) = true
let concretize = FjConcreteConcretization.concretize
let techniques = FjConcreteIllTyped.techniques
