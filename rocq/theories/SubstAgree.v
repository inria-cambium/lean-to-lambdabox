(** * SubstAgree.v

    Substitution commutes with the translation: the Lean-side substitution used
    by [WcbvEval] and MetaRocq's [ECSubst]/[csubst] agree under [Translate].
    Key lemma feeding the beta/delta cases of the simulation. *)
