type 'prototerm rule =
    string * int list * int * ('prototerm list -> bool) * ('prototerm list -> 'prototerm Seq.t)

module type LANGUAGE = sig
    type prototerm
    type fact

    val sort_count     : int
    val prototerm_sort : prototerm -> int
    val output_sorts   : int list

    type prototerm_key
    type fact_key
    val prototerm_key         : prototerm -> prototerm_key
    val fact_key              : fact -> fact_key
    val compare_prototerm_key : prototerm_key -> prototerm_key -> int
    val compare_fact_key      : fact_key -> fact_key -> int

    val fact_depth         : fact -> int
    val fact_nodes         : fact -> int
    val fact_unique_vars   : fact -> int
    val prototerm_min_size : prototerm -> int

    type config
    val parse_config : (string * string) list -> config

    type seed_state
    val initial_seeds : seed_state
    val next_seed     : config -> seed_state -> (prototerm * seed_state) option

    val rules      : config -> prototerm rule list
    val concretize : search_budget:int option -> config -> prototerm -> fact Seq.t

    val techniques : (config -> prototerm -> prototerm Seq.t) list
end
