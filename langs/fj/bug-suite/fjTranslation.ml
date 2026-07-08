module L = FjPrograms

let to_testable term_kind (f : L.tagged_fact) : L.tagged_fact option =
    match term_kind with
    | Generator.Well_typed -> Some f
    | Generator.Ill_typed  -> if FjTypechecker.check f then None else Some f

let to_testable_oracle term_kind (f : L.tagged_fact) : L.tagged_fact option =
    match term_kind with
    | Generator.Well_typed -> if FjTypechecker.check f then Some f else None
    | Generator.Ill_typed  -> if FjTypechecker.check f then None else Some f
