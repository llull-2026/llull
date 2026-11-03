let to_testable (_term_kind : Generator.term_kind) (f : CombPrograms.fact)
        : CombPrograms.fact option =
    Some f

let to_testable_oracle (term_kind : Generator.term_kind) (f : CombPrograms.fact)
        : CombPrograms.fact option =
    match term_kind with
    | Generator.Well_typed ->
        if CombTypechecker.agrees_with_fact f then Some f else None
    | Generator.Ill_typed ->
        if CombTypechecker.agrees_with_fact f then None else Some f
