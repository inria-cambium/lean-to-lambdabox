(** * Backward.v — backward simulation (roadmap).

    [eval (TEnv Γ) fl (T t) v'  ->  exists v, v' = T v /\ WcbvEvalT-restated Γ fl t v]
    at [with_constructor_as_block = false], on the wf fragment (Wf.v). Every
    MetaRocq [EWcbvEval.eval] step whose subject is in the image of [T] is matched by
    a restated Lean derivation; the [EAst]-only nodes ([tVar]/[tEvar]/[tCoFix]/
    [tLazy]/[tForce], and [tConstruct] over-applications) are ruled out because they
    are not in the image of [T] (T_inj / the restatement omits them). Uses
    [SubstAgree.T_subst] (+ the closed-substl upgrade, Wf.v) for β/ζ/δ/ι/fix and
    [EnvAgree]/[ValuesAgree] for δ/ι/proj/construct. Set→Type elimination is fine
    ([eval] is [Set]-valued). Not started; depends on Wf + EnvAgree + ValuesAgree. *)
