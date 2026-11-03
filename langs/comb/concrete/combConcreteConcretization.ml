open CombPrograms
open CombConcretePrototerms

let concretize ~search_budget:_ (_ : config) s : fact Seq.t =
    if s.sctx <> [] || s.stylvl <> 0 then Seq.empty
    else Seq.return { term = s.sterm; typ = s.styp; bindings = [] }
