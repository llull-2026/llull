open HephPrograms
module T = HephTypechecker
module P = HephPrototerms

type cprog = {
    classes : concrete_class list;
    methods : concrete_method list;
    main : (term * heph_type) option;
    next_class_label : int;
    next_fl : int;
    next_ml : int;
}

type cexpr = {
    snap_classes : concrete_class list;
    snap_methods : concrete_method list;
    scope : int;
    ctx : heph_type IntMap.t;
    term : term;
    typ : heph_type;
    next_sym : int;
}

type prototerm =
    | Prog of cprog
    | Expr of cexpr
    | Faulted of tagged_fact

type fact = tagged_fact

let sort_program = 0
let sort_expr = 1
let sort_count = 2
let prototerm_sort = function
    | Prog _ | Faulted _ -> sort_program
    | Expr _ -> sort_expr
let output_sorts = [sort_program]

type prototerm_key =
    | PK of concrete_class list * concrete_method list * (term * heph_type) option
    | EK of concrete_class list * concrete_method list * int
            * (int * heph_type) list * term * heph_type
    | FK of string
type fact_key = string

let prototerm_key = function
    | Prog p -> PK (p.classes, p.methods, p.main)
    | Expr e -> EK (e.snap_classes, e.snap_methods, e.scope,
                    IntMap.bindings e.ctx, e.term, e.typ)
    | Faulted f -> FK f.tf_rendered
let fact_key (f : tagged_fact) = Digest.string f.tf_rendered
let compare_prototerm_key = compare
let compare_fact_key = compare

let fact_depth = HephPrograms.fact_depth
let fact_nodes = HephPrograms.fact_nodes
let fact_unique_vars = HephPrograms.fact_unique_vars

let rec term_nodes = function
    | Var _ | BVar _ -> 1
    | New (_, args) -> 1 + List.fold_left (fun a t -> a + term_nodes t) 0 args
    | FieldAccess (e, _) | Lambda (_, e) -> 1 + term_nodes e
    | MethodInvoke (e, _, args) ->
        1 + term_nodes e + List.fold_left (fun a t -> a + term_nodes t) 0 args
    | If (_, c, t, e) | Cond (c, t, e) -> 1 + term_nodes c + term_nodes t + term_nodes e

let prototerm_min_size = function
    | Prog p -> (match p.main with Some (t, _) -> term_nodes t | None -> 1)
    | Expr e -> term_nodes e.term
    | Faulted f -> term_nodes f.tf_main_term

type config = P.config
let parse_config = HephGenerator.parse_config

let to_h2 (p : cprog) : P.program_proto_term =
    { (P.make_empty_program ()) with
      P.classes = List.map (fun cc ->
          { P.cl_label = cc.cc_label; cl_tparams = cc.cc_tparams;
            cl_parent = cc.cc_parent; cl_fields = cc.cc_fields }) p.classes;
      next_class_label = p.next_class_label;
      next_fl = p.next_fl }

let of_h2 (p : cprog) (h : P.program_proto_term) : cprog =
    { p with
      classes = List.map (fun (ce : P.class_entry) ->
          { cc_label = ce.cl_label; cc_tparams = ce.cl_tparams;
            cc_parent = ce.cl_parent; cc_fields = ce.cl_fields }) h.P.classes;
      next_class_label = h.P.next_class_label;
      next_fl = h.P.next_fl }

let empty_prog = { classes = []; methods = []; main = None;
                   next_class_label = 0; next_fl = 0; next_ml = 0 }

let this_type (cc : concrete_class) =
    TyClass (Synth cc.cc_label, List.init (List.length cc.cc_tparams) (fun i -> TyParam i))

let basis (config : config) classes scope =
    let h = to_h2 { empty_prog with classes } in
    let pool = HephConcretization.types_up_to h ~scope_tparams:scope config.P.max_type_depth in
    let this_tys = List.filter_map (fun cc ->
        if scope > 0 && List.length cc.cc_tparams = scope then Some (this_type cc) else None) classes in
    List.fold_left (fun acc t -> if List.mem t acc then acc else acc @ [t]) [] (pool @ this_tys)

let scopes classes =
    List.sort_uniq compare (0 :: List.map (fun cc -> List.length cc.cc_tparams) classes)

let is_sub classes a b = T.is_subtype classes a b

let leaf p scope ctx term typ next_sym =
    { snap_classes = p.classes; snap_methods = p.methods; scope; ctx; term; typ; next_sym }

let try_var config p =
    List.concat_map (fun scope ->
        List.map (fun t -> leaf p scope (IntMap.singleton 0 t) (Var 0) t 1)
            (basis config p.classes scope)) (scopes p.classes)

let zero_field classes = function
    | TyClass (cr, args) -> T.fields_of classes cr args = []
    | _ -> false

let try_new0 config p =
    List.concat_map (fun scope ->
        List.filter_map (fun t ->
            if zero_field p.classes t then Some (leaf p scope IntMap.empty (New (t, [])) t 0)
            else None) (basis config p.classes scope)) (scopes p.classes)

let try_field e =
    match e.typ with
    | TyClass (cr, args) ->
        List.map (fun (fl, ft) -> { e with term = FieldAccess (e.term, fl); typ = ft })
            (T.fields_of e.snap_classes cr args)
    | _ -> []

let rec shift_vars off = function
    | Var i -> Var (i + off)
    | BVar _ as t -> t
    | New (ty, args) -> New (ty, List.map (shift_vars off) args)
    | FieldAccess (e, fl) -> FieldAccess (shift_vars off e, fl)
    | MethodInvoke (e, ml, args) -> MethodInvoke (shift_vars off e, ml, List.map (shift_vars off) args)
    | Lambda (ty, b) -> Lambda (ty, shift_vars off b)
    | If (ty, c, t, e) -> If (ty, shift_vars off c, shift_vars off t, shift_vars off e)
    | Cond (c, t, e) -> Cond (shift_vars off c, shift_vars off t, shift_vars off e)

let merge = function
    | [] -> None
    | first :: rest ->
        if not (List.for_all (fun e ->
                e.scope = first.scope
                && e.snap_classes = first.snap_classes
                && e.snap_methods = first.snap_methods) rest) then None
        else
            let (terms, ctx, next) = List.fold_left (fun (ts, ctx, off) e ->
                let ctx' = IntMap.fold (fun i t m -> IntMap.add (i + off) t m) e.ctx ctx in
                (shift_vars off e.term :: ts, ctx', off + e.next_sym))
                ([first.term], first.ctx, first.next_sym) rest in
            Some (List.rev terms, { first with ctx; next_sym = next })

let try_new_k config args =
    match merge args with
    | None -> []
    | Some (terms, m) ->
        let classes = m.snap_classes in
        List.filter_map (fun t ->
            match t with
            | TyClass (cr, cargs) ->
                let fs = T.fields_of classes cr cargs in
                if List.length fs = List.length args
                   && List.for_all2 (fun (_, ft) a -> is_sub classes a.typ ft) fs args
                then Some { m with term = New (t, terms); typ = t }
                else None
            | _ -> None) (basis config classes m.scope)

let method_labels methods =
    -1 :: List.sort_uniq compare (List.map (fun me -> me.cm_label) methods)

let try_invoke_k recv args =
    match recv.typ, merge (recv :: args) with
    | TyClass (cr, cargs), Some (rt :: ats, m) ->
        List.filter_map (fun ml ->
            match T.lookup_method m.snap_classes m.snap_methods cr cargs ml with
            | Some (ps, ret) when List.length ps = List.length args
                    && List.for_all2 (fun a pt -> is_sub m.snap_classes a.typ pt) args ps ->
                Some { m with term = MethodInvoke (rt, ml, ats); typ = ret }
            | _ -> None) (method_labels m.snap_methods)
    | _ -> []

let rec rename_var j i = function
    | Var k -> Var (if k = j then i else k)
    | BVar _ as t -> t
    | New (ty, args) -> New (ty, List.map (rename_var j i) args)
    | FieldAccess (e, fl) -> FieldAccess (rename_var j i e, fl)
    | MethodInvoke (e, ml, args) -> MethodInvoke (rename_var j i e, ml, List.map (rename_var j i) args)
    | Lambda (ty, b) -> Lambda (ty, rename_var j i b)
    | If (ty, c, t, e) -> If (ty, rename_var j i c, rename_var j i t, rename_var j i e)
    | Cond (c, t, e) -> Cond (rename_var j i c, rename_var j i t, rename_var j i e)

let try_contract e =
    let vars = IntMap.bindings e.ctx in
    List.concat_map (fun (i, ti) ->
        List.filter_map (fun (j, tj) ->
            if j > i && T.type_equal ti tj
            then Some { e with term = rename_var j i e.term; ctx = IntMap.remove j e.ctx }
            else None) vars) vars

let rec bind_var id depth = function
    | Var k when k = id -> BVar depth
    | (Var _ | BVar _) as t -> t
    | New (ty, args) -> New (ty, List.map (bind_var id depth) args)
    | FieldAccess (e, fl) -> FieldAccess (bind_var id depth e, fl)
    | MethodInvoke (e, ml, args) -> MethodInvoke (bind_var id depth e, ml, List.map (bind_var id depth) args)
    | Lambda (ty, b) -> Lambda (ty, bind_var id (depth + 1) b)
    | If (ty, c, t, e) -> If (ty, bind_var id depth c, bind_var id depth t, bind_var id depth e)
    | Cond (c, t, e) -> Cond (bind_var id depth c, bind_var id depth t, bind_var id depth e)

let try_lambda e =
    List.map (fun (id, t) ->
        { e with term = Lambda (t, bind_var id 0 e.term);
                 typ = TyClass (Prelude "Function", [t; e.typ]);
                 ctx = IntMap.remove id e.ctx }) (IntMap.bindings e.ctx)

let boolean = TyClass (Prelude "Boolean", [])

let try_if config c t e =
    match merge [c; t; e] with
    | Some ([ct; tt; et], m) when is_sub m.snap_classes c.typ boolean ->
        List.filter_map (fun r ->
            if is_sub m.snap_classes t.typ r && is_sub m.snap_classes e.typ r
            then Some { m with term = If (r, ct, tt, et); typ = r }
            else None) (basis config m.snap_classes m.scope)
    | _ -> []

let bounds_ok p = T.classtable_bounds_ok p.classes

let try_add_class config p =
    if p.main <> None then []
    else List.filter bounds_ok (List.of_seq (Seq.map (of_h2 p)
        (P.try_add_class ~max_identical:config.P.max_identical_classes (to_h2 p))))

let try_add_field p =
    if p.main <> None || p.methods <> [] then []
    else List.filter bounds_ok (List.map (of_h2 p) (P.try_add_field (to_h2 p)))

let built_on p e = e.snap_classes = p.classes && e.snap_methods = p.methods

let try_materialize_method p e =
    if p.main <> None || not (built_on p e) then []
    else
        let h = to_h2 p in
        List.concat_map (fun cc ->
            if List.length cc.cc_tparams <> e.scope then []
            else
                let this_t = this_type cc in
                List.filter_map (fun (this_sym, t) ->
                    if not (T.type_equal t this_t) then None
                    else
                        let params = List.filter (fun (s, _) -> s <> this_sym) (IntMap.bindings e.ctx) in
                        if List.for_all (fun (_, pt) ->
                               P.variance_check_type h cc.cc_tparams Contravariant pt) params
                           && P.variance_check_type h cc.cc_tparams Covariant e.typ
                        then
                            let me = { cm_class = cc.cc_label; cm_label = p.next_ml;
                                       cm_this_sym = this_sym; cm_tparams = [];
                                       cm_params = params; cm_return = e.typ;
                                       cm_body = e.term; cm_default = None } in
                            Some { p with methods = me :: p.methods; next_ml = p.next_ml + 1 }
                        else None) (IntMap.bindings e.ctx)) p.classes

let try_assign_main p e =
    if p.main <> None || e.scope <> 0 || not (built_on p e) then []
    else if not (IntMap.for_all (fun _ t -> zero_field p.classes t) e.ctx) then []
    else
        let closed = IntMap.fold (fun id t term ->
            let rec close = function
                | Var k when k = id -> New (t, [])
                | (Var _ | BVar _) as x -> x
                | New (ty, args) -> New (ty, List.map close args)
                | FieldAccess (x, fl) -> FieldAccess (close x, fl)
                | MethodInvoke (x, ml, args) -> MethodInvoke (close x, ml, List.map close args)
                | Lambda (ty, b) -> Lambda (ty, close b)
                | If (ty, c, a, b) -> If (ty, close c, close a, close b)
                | Cond (c, a, b) -> Cond (close c, close a, close b) in
            close term) e.ctx e.term in
        [{ p with main = Some (closed, e.typ) }]

let render_method me =
    string_of_type me.cm_return ^ " " ^ ml_name me.cm_label ^ "(" ^
    String.concat ", " (List.map (fun (s, t) -> string_of_type t ^ " x" ^ string_of_int s) me.cm_params)
    ^ ") { return " ^ string_of_term me.cm_body ^ "; }"

let render_class methods cc =
    let object_bound = TyClass (Prelude "Object", []) in
    let tps = if cc.cc_tparams = [] then "" else
        "<" ^ String.concat ", " (List.mapi (fun i (tp : tparam_proto_term) ->
            let base = string_of_variance tp.tp_variance ^ "P" ^ string_of_int i in
            if tp.tp_bound = object_bound then base
            else base ^ " extends " ^ string_of_type tp.tp_bound) cc.cc_tparams) ^ ">" in
    let (pcr, pargs) = cc.cc_parent in
    let par = string_of_class_ref pcr ^
        (if pargs = [] then "" else "<" ^ String.concat ", " (List.map string_of_type pargs) ^ ">") in
    let members =
        List.map (fun (fl, ft) -> string_of_type ft ^ " " ^ fl_name fl ^ ";") cc.cc_fields
        @ List.map render_method (List.filter (fun me -> me.cm_class = cc.cc_label) methods) in
    "class " ^ string_of_class_ref (Synth cc.cc_label) ^ tps ^ " extends " ^ par ^ " {"
    ^ String.concat "" (List.map (fun m -> " " ^ m) members) ^ " }"

let fact_of_parts classes methods main_term main_type =
    let buf = Buffer.create 256 in
    List.iter (fun cc -> Buffer.add_string buf (render_class methods cc ^ "\n")) (List.rev classes);
    Buffer.add_string buf ("main: " ^ string_of_term main_term ^ " : " ^ string_of_type main_type);
    { tf_classes = classes; tf_methods = methods;
      tf_main_term = main_term; tf_main_type = main_type;
      tf_bindings = []; tf_rendered = Buffer.contents buf }

let object_ty = TyClass (Prelude "Object", [])

let fact_of_prog p =
    let (mt, mty) = match p.main with Some m -> m | None -> (New (object_ty, []), object_ty) in
    fact_of_parts p.classes p.methods mt mty

let show_rejected = Sys.getenv_opt "HEPH2C_SHOW_REJECTED" <> None

let concretize ~search_budget:_ (_ : config) = function
    | Prog p ->
        let f = fact_of_prog p in
        if show_rejected && not (T.check f) then prerr_endline ("[rejected]\n" ^ f.tf_rendered);
        Seq.return f
    | Faulted f -> Seq.return f
    | Expr _ -> Seq.empty

let rules (config : config) : prototerm Language.rule list =
    let progs ps = Seq.map (fun p -> Prog p) (List.to_seq ps) in
    let exprs es = Seq.map (fun e -> Expr e) (List.to_seq es) in
    let always _ = true in
    let open_prog = function Prog p :: _ -> p.main = None | _ -> false in
    [
        ("var", [sort_program], sort_expr, open_prog,
         (function [Prog p] -> exprs (try_var config p) | _ -> Seq.empty));
        ("new0", [sort_program], sort_expr, open_prog,
         (function [Prog p] -> exprs (try_new0 config p) | _ -> Seq.empty));
        ("field", [sort_expr], sort_expr, always,
         (function [Expr e] -> exprs (try_field e) | _ -> Seq.empty));
        ("new_1", [sort_expr], sort_expr, always,
         (function [Expr a] -> exprs (try_new_k config [a]) | _ -> Seq.empty));
        ("new_2", [sort_expr; sort_expr], sort_expr, always,
         (function [Expr a; Expr b] -> exprs (try_new_k config [a; b]) | _ -> Seq.empty));
        ("invoke_0", [sort_expr], sort_expr, always,
         (function [Expr r] -> exprs (try_invoke_k r []) | _ -> Seq.empty));
        ("invoke_1", [sort_expr; sort_expr], sort_expr, always,
         (function [Expr r; Expr a] -> exprs (try_invoke_k r [a]) | _ -> Seq.empty));
        ("invoke_2", [sort_expr; sort_expr; sort_expr], sort_expr, always,
         (function [Expr r; Expr a; Expr b] -> exprs (try_invoke_k r [a; b]) | _ -> Seq.empty));
        ("contract", [sort_expr], sort_expr,
         (function [Expr e] -> IntMap.cardinal e.ctx >= 2 | _ -> false),
         (function [Expr e] -> exprs (try_contract e) | _ -> Seq.empty));
        ("lambda", [sort_expr], sort_expr, always,
         (function [Expr e] -> exprs (try_lambda e) | _ -> Seq.empty));
        ("if", [sort_expr; sort_expr; sort_expr], sort_expr, always,
         (function [Expr c; Expr t; Expr e] -> exprs (try_if config c t e) | _ -> Seq.empty));
        ("main_from_expr", [sort_program; sort_expr], sort_program, open_prog,
         (function [Prog p; Expr e] -> progs (try_assign_main p e) | _ -> Seq.empty));
        ("add_class", [sort_program], sort_program, open_prog,
         (function [Prog p] -> progs (try_add_class config p) | _ -> Seq.empty));
        ("add_field", [sort_program], sort_program,
         (function Prog p :: _ -> p.main = None && p.classes <> [] && p.methods = [] | _ -> false),
         (function [Prog p] -> progs (try_add_field p) | _ -> Seq.empty));
        ("materialize_method", [sort_program; sort_expr], sort_program,
         (function Prog p :: _ -> p.main = None && p.classes <> [] | _ -> false),
         (function [Prog p; Expr e] -> progs (try_materialize_method p e) | _ -> Seq.empty));
    ]

type seed_state = int
let initial_seeds = 0
let next_seed _config = function
    | 0 -> Some (Prog empty_prog, 1)
    | _ -> None

let rec perturbations classes methods (t : term) : term list =
    let field_labels = List.sort_uniq compare
        (List.concat_map (fun cc -> List.map fst cc.cc_fields) classes) in
    let class_tys = object_ty :: List.map this_type classes in
    let here = match t with
        | Var _ | BVar _ -> []
        | New (ty, args) ->
            List.filter_map (fun ty' -> if ty' = ty then None else Some (New (ty', args))) class_tys
            @ (if args = [] then [] else [New (ty, List.filteri (fun i _ -> i < List.length args - 1) args)])
        | FieldAccess (e, fl) ->
            List.filter_map (fun fl' -> if fl' = fl then None else Some (FieldAccess (e, fl'))) field_labels
            @ [FieldAccess (New (object_ty, []), fl)]
        | MethodInvoke (e, ml, args) ->
            List.filter_map (fun ml' -> if ml' = ml then None else Some (MethodInvoke (e, ml', args)))
                (method_labels methods)
            @ [MethodInvoke (New (object_ty, []), ml, args)]
            @ (if args = [] then [] else [MethodInvoke (e, ml, List.filteri (fun i _ -> i < List.length args - 1) args)])
        | Lambda (ty, b) ->
            List.filter_map (fun ty' -> if ty' = ty then None else Some (Lambda (ty', b))) class_tys
        | If (ty, c, a, b) ->
            List.filter_map (fun ty' -> if ty' = ty then None else Some (If (ty', c, a, b))) class_tys
            @ [If (ty, New (object_ty, []), a, b)]
        | Cond _ -> [] in
    let sub = perturbations classes methods in
    let set l i x = List.mapi (fun j y -> if i = j then x else y) l in
    let in_list mk args = List.concat (List.mapi (fun i a -> List.map (fun a' -> mk (set args i a')) (sub a)) args) in
    let below = match t with
        | Var _ | BVar _ | Cond _ -> []
        | New (ty, args) -> in_list (fun a -> New (ty, a)) args
        | FieldAccess (e, fl) -> List.map (fun e' -> FieldAccess (e', fl)) (sub e)
        | MethodInvoke (e, ml, args) ->
            List.map (fun e' -> MethodInvoke (e', ml, args)) (sub e)
            @ in_list (fun a -> MethodInvoke (e, ml, a)) args
        | Lambda (ty, b) -> List.map (fun b' -> Lambda (ty, b')) (sub b)
        | If (ty, c, a, b) ->
            List.map (fun c' -> If (ty, c', a, b)) (sub c)
            @ List.map (fun a' -> If (ty, c, a', b)) (sub a)
            @ List.map (fun b' -> If (ty, c, a, b')) (sub b) in
    here @ below

let max_perturbations = 256

let perturbed_facts p =
    let (mt, mty) = match p.main with Some m -> m | None -> (New (object_ty, []), object_ty) in
    let mains = List.map (fun mt' -> fact_of_parts p.classes p.methods mt' mty)
        (perturbations p.classes p.methods mt) in
    let bodies = List.concat (List.mapi (fun k me ->
        List.map (fun b' ->
            let methods = List.mapi (fun j m -> if j = k then { m with cm_body = b' } else m) p.methods in
            fact_of_parts p.classes methods mt mty)
            (perturbations p.classes p.methods me.cm_body)) p.methods) in
    List.filteri (fun i _ -> i < max_perturbations) (mains @ bodies)

let bound_violation_technique (_ : config) = function
    | Prog p when Hashtbl.hash_param 4096 65536 (p.classes, p.methods, p.main)
                  land (HephIllTyped.bound_gate - 1) = 0 ->
        let h = to_h2 p in
        HephIllTyped.bound_violating_classes h
        |> List.filteri (fun i _ -> i < HephIllTyped.max_bound_violations)
        |> List.map (fun (ce : P.class_entry) ->
            let cc = { cc_label = ce.cl_label; cc_tparams = ce.cl_tparams;
                       cc_parent = ce.cl_parent; cc_fields = ce.cl_fields } in
            Faulted (fact_of_prog { p with classes = cc :: p.classes;
                                           next_class_label = p.next_class_label + 1 }))
        |> List.to_seq
    | _ -> Seq.empty

let techniques = [
    bound_violation_technique;
    (fun (_ : config) -> function
        | Prog p ->
            Helper.interleave [
                Seq.map (fun f -> Faulted f) (List.to_seq (perturbed_facts p));
                Seq.map (fun f -> Faulted f) (HephIllTyped.all_main_mutations (fact_of_prog p))]
        | _ -> Seq.empty);
]
