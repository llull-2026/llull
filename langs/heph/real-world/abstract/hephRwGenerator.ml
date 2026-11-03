open HephRwPrograms
open HephRwPrototerms

type prototerm = HephRwPrototerms.prototerm
type fact = HephRwPrototerms.fact

let sort_count = HephRwPrototerms.sort_count
let prototerm_sort = HephRwPrototerms.prototerm_sort
let output_sorts = HephRwPrototerms.output_sorts

type prototerm_key = HephRwPrototerms.prototerm_key
type fact_key = HephRwPrototerms.fact_key
let prototerm_key = HephRwPrototerms.prototerm_key
let fact_key = HephRwPrototerms.fact_key
let compare_prototerm_key = HephRwPrototerms.compare_prototerm_key
let compare_fact_key = HephRwPrototerms.compare_fact_key

let fact_depth = HephRwPrograms.fact_depth
let fact_nodes = HephRwPrograms.fact_nodes
let fact_unique_vars = HephRwPrograms.fact_unique_vars
let prototerm_min_size = HephRwPrototerms.prototerm_min_size

type config = HephRwPrototerms.config
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
      max_identical_classes = int_of "max_identical_classes" 0;
      rich_methods = bool_of "rich_methods" false;
      resolve_method_sigs = bool_of "resolve_method_sigs" true;
      class_sampling = bool_of "class_sampling" true;
      scoped_bounds = bool_of "scoped_bounds" true;
      approx_field_reads = bool_of "approx_field_reads" true;
      multi_wildcards = bool_of "multi_wildcards" true;
      tvar_wildcard_fields = bool_of "tvar_wildcard_fields" true;
      explicit_news = bool_of "explicit_news" true;
      generic_methods = bool_of "generic_methods" true;
      mutate_return = bool_of "mutate_return" true;
      randomize_breaks = bool_of "randomize_breaks" true }

let all_seeds_ms = [
    ExprProtoTerm (make_var_proto_term ());
    ExprProtoTerm (make_prelude_new "Object");
    ExprProtoTerm (make_prelude_new "Number");
    ExprProtoTerm (make_prelude_new "Integer");
    ExprProtoTerm (make_prelude_new "String");
    ExprProtoTerm (make_prelude_new "Boolean");
    ExprProtoTerm (make_new0 ());
    ExprProtoTerm (make_null ());
    ProgramProtoTerm (make_empty_program ());
]

type seed_state = int
let initial_seeds = 0
let next_seed _config idx =
    if idx < List.length all_seeds_ms then
        Some (List.nth all_seeds_ms idx, idx + 1)
    else None

let rules (config : config) : prototerm Language.rule list =
    let progs ps = Seq.map (fun p -> ProgramProtoTerm p) (List.to_seq ps) in
    let progs_seq ps = Seq.map (fun p -> ProgramProtoTerm p) ps in
    let exprs es = Seq.map (fun e -> ExprProtoTerm e) (List.to_seq es) in
    let always _ = true in
    let within_tvars expand inputs =
        Seq.filter (fun pt -> prototerm_tvar_count pt <= config.max_tvars)
            (expand inputs) in
    let rich_rules = if not config.rich_methods then [] else [
        ("cond_dup", [sort_expr], sort_expr, always,
         (function [ExprProtoTerm s] -> exprs (try_cond_dup s) | _ -> Seq.empty));
    ] in
    List.map (fun (name, ins, out, suit, expand) ->
        (name, ins, out, suit, within_tvars expand))
    ([
        ("add_class", [sort_program], sort_program, always,
         (function [ProgramProtoTerm p] ->
              progs_seq (try_add_class ~max_identical:config.max_identical_classes
                  ~sample:config.class_sampling p)
            | _ -> Seq.empty));
        ("add_field", [sort_program], sort_program,
         (function [ProgramProtoTerm p] -> p.classes <> [] | _ -> false),
         (function [ProgramProtoTerm p] ->
              progs (try_add_field ~tvar_wild:config.tvar_wildcard_fields
                  ~scoped:config.scoped_bounds p)
            | _ -> Seq.empty));
        ("field", [sort_expr], sort_expr, always,
         (function [ExprProtoTerm s] -> exprs (try_field_access s) | _ -> Seq.empty));
        ("new_1", [sort_expr], sort_expr, always,
         (function [ExprProtoTerm s] -> exprs (try_new_k [s]) | _ -> Seq.empty));
        ("new_2", [sort_expr; sort_expr], sort_expr, always,
         (function [ExprProtoTerm s1; ExprProtoTerm s2] -> exprs (try_new_k [s1; s2]) | _ -> Seq.empty));
        ("invoke_0", [sort_expr], sort_expr, always,
         (function [ExprProtoTerm r] -> exprs (try_invoke_k r []) | _ -> Seq.empty));
        ("invoke_1", [sort_expr; sort_expr], sort_expr, always,
         (function [ExprProtoTerm r; ExprProtoTerm a] -> exprs (try_invoke_k r [a]) | _ -> Seq.empty));
        ("invoke_2", [sort_expr; sort_expr; sort_expr], sort_expr, always,
         (function [ExprProtoTerm r; ExprProtoTerm a1; ExprProtoTerm a2] -> exprs (try_invoke_k r [a1; a2]) | _ -> Seq.empty));
        ("contract", [sort_expr], sort_expr,
         (function [ExprProtoTerm s] -> IntMap.cardinal s.sym_map >= 2 | _ -> false),
         (function [ExprProtoTerm s] -> exprs (try_contract s) | _ -> Seq.empty));
        ("lambda", [sort_expr], sort_expr, always,
         (function [ExprProtoTerm s] -> exprs (try_lambda s) | _ -> Seq.empty));
        ("cond", [sort_expr; sort_expr; sort_expr], sort_expr, always,
         (function [ExprProtoTerm c; ExprProtoTerm t; ExprProtoTerm e] ->
              exprs (try_cond c t e) | _ -> Seq.empty));
        ("array_1", [sort_expr], sort_expr, always,
         (function [ExprProtoTerm e] -> exprs (try_array [e]) | _ -> Seq.empty));
        ("array_2", [sort_expr; sort_expr], sort_expr, always,
         (function [ExprProtoTerm a; ExprProtoTerm b] ->
              exprs (try_array [a; b]) | _ -> Seq.empty));
        ("assign_main", [sort_program; sort_expr], sort_program,
         (function ProgramProtoTerm p :: _ -> p.main = None | _ -> false),
         (function [ProgramProtoTerm p; ExprProtoTerm e] -> progs (try_assign_main p e) | _ -> Seq.empty));
        ("materialize_method", [sort_program; sort_expr], sort_program,
         (function ProgramProtoTerm p :: _ -> p.classes <> [] | _ -> false),
         (function [ProgramProtoTerm p; ExprProtoTerm e] ->
              progs (try_materialize_method ~rich:config.rich_methods
                  ~generic:config.generic_methods p e) | _ -> Seq.empty));
    ] @ rich_rules)

let concretize ~search_budget config = function
    | FaultedProgram (p, fault) -> HephRwIllTyped.ground_fault ~search_budget config p fault
    | s -> HephRwConcretization.concretize ~search_budget config s

let techniques = HephRwIllTyped.techniques

let concretize_steps ~search_budget:_ config = function
    | FaultedProgram (p, fault) -> HephRwIllTyped.ground_fault_steps config p fault
    | s -> HephRwConcretization.concretize_steps config s
