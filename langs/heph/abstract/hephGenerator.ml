open HephPrograms
open HephPrototerms

type prototerm = HephPrototerms.prototerm
type fact = HephPrototerms.fact

let sort_count = HephPrototerms.sort_count
let prototerm_sort = HephPrototerms.prototerm_sort
let output_sorts = HephPrototerms.output_sorts

type prototerm_key = HephPrototerms.prototerm_key
type fact_key = HephPrototerms.fact_key
let prototerm_key = HephPrototerms.prototerm_key
let fact_key = HephPrototerms.fact_key
let compare_prototerm_key = HephPrototerms.compare_prototerm_key
let compare_fact_key = HephPrototerms.compare_fact_key

let fact_depth = HephPrograms.fact_depth
let fact_nodes = HephPrograms.fact_nodes
let fact_unique_vars = HephPrograms.fact_unique_vars
let prototerm_min_size = HephPrototerms.prototerm_min_size

type config = HephConcretization.config
let parse_config = HephConcretization.parse_config

let all_seeds_ms = [
    ExprProtoTerm (make_var_proto_term ());
    ExprProtoTerm (make_prelude_new "Object");
    ExprProtoTerm (make_prelude_new "Number");
    ExprProtoTerm (make_prelude_new "Integer");
    ExprProtoTerm (make_prelude_new "String");
    ExprProtoTerm (make_prelude_new "Boolean");
    ExprProtoTerm (make_new0 ());
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
    [
        ("add_class", [sort_program], sort_program, always, (function [ProgramProtoTerm p] ->
              progs_seq (try_add_class ~max_identical:config.HephConcretization.max_identical_classes p)
            | _ -> Seq.empty));
        ("add_field", [sort_program], sort_program, (function [ProgramProtoTerm p] -> p.classes <> [] | _ -> false), (function [ProgramProtoTerm p] -> progs (try_add_field p) | _ -> Seq.empty));
        ("field", [sort_expr], sort_expr, always, (function [ExprProtoTerm s] -> exprs (try_field_access s) | _ -> Seq.empty));
        ("new_1", [sort_expr], sort_expr, always, (function [ExprProtoTerm s] -> exprs (try_new_k [s]) | _ -> Seq.empty));
        ("new_2", [sort_expr; sort_expr], sort_expr, always, (function [ExprProtoTerm s1; ExprProtoTerm s2] -> exprs (try_new_k [s1; s2]) | _ -> Seq.empty));
        ("invoke_0", [sort_expr], sort_expr, always, (function [ExprProtoTerm r] -> exprs (try_invoke_k r []) | _ -> Seq.empty));
        ("invoke_1", [sort_expr; sort_expr], sort_expr, always, (function [ExprProtoTerm r; ExprProtoTerm a] -> exprs (try_invoke_k r [a]) | _ -> Seq.empty));
        ("invoke_2", [sort_expr; sort_expr; sort_expr], sort_expr, always, (function [ExprProtoTerm r; ExprProtoTerm a1; ExprProtoTerm a2] -> exprs (try_invoke_k r [a1; a2]) | _ -> Seq.empty));
        ("contract", [sort_expr], sort_expr, (function [ExprProtoTerm s] -> IntMap.cardinal s.sym_map >= 2 | _ -> false), (function [ExprProtoTerm s] -> exprs (try_contract s) | _ -> Seq.empty));
        ("lambda", [sort_expr], sort_expr, always, (function [ExprProtoTerm s] -> exprs (try_lambda s) | _ -> Seq.empty));
        ("assign_main", [sort_program; sort_expr], sort_program, (function ProgramProtoTerm p :: _ -> p.main = None | _ -> false), (function [ProgramProtoTerm p; ExprProtoTerm e] -> progs (try_assign_main p e) | _ -> Seq.empty));
        ("materialize_method", [sort_program; sort_expr], sort_program, (function ProgramProtoTerm p :: _ -> p.classes <> [] | _ -> false), (function [ProgramProtoTerm p; ExprProtoTerm e] -> progs (try_materialize_method p e) | _ -> Seq.empty));
    ]

let concretize ~search_budget config = function
    | FaultedProgram (p, fault) -> HephIllTyped.ground_fault ~search_budget config p fault
    | s -> HephConcretization.concretize ~search_budget config s

let techniques = HephIllTyped.techniques
