type fact = HephRwPrograms.tagged_fact
type raw_fact = HephRwPrograms.tagged_fact

let to_testable term_kind (f : raw_fact) : fact option =
    match term_kind with
    | Generator.Well_typed -> if HephRwTypechecker.check f then Some f else None
    | Generator.Ill_typed  -> if HephRwTypechecker.check f then None else Some f
