type fact = HephPrograms.tagged_fact
type raw_fact = HephPrograms.tagged_fact

let to_testable term_kind (f : raw_fact) : fact option =
    match term_kind with
    | Generator.Well_typed -> Some f
    | Generator.Ill_typed  -> if HephTypechecker.check f then None else Some f
