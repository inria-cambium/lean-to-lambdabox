(** * Forward.v — forward simulation (roadmap).

    [WcbvEvalT-restated Γ fl t v  ->  eval (TEnv Γ) fl (T t) (T v)] at
    [with_constructor_as_block = false], on the wf fragment (Wf.v). Each restated
    rule maps to its [EWcbvEval.eval] constructor; the β/ζ/δ/ι/fix cases discharge
    the substitution side conditions via [SubstAgree.T_subst] + the closed-substl
    upgrade (Wf.v), and δ/ι/proj/construct via [EnvAgree] ([envLookup ↔ lookup_env],
    [constructorArity ↔ cstr_arity]) + [ValuesAgree] (spine/[value_head]). Since the
    restated [LBTerm]/eval are hand-written, the derivation is by structural
    recursion on the restated relation (no [rocq-lean-import] recursor). Not started;
    depends on Wf + EnvAgree + ValuesAgree. *)
