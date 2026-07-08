(** * EnvAgree.v — environment/arity agreement (roadmap).

    Global-environment lookup on the restated Lean side ([envLookup], comparing the
    full kername via [Kername.beq]) matches MetaRocq [EGlobalEnv.lookup_env] (via
    [eq_kername]) under the environment translation, and [constructorArity]
    ([npars + nargs]) matches [EAst.cstr_arity] ([ind_npars + cstr_nargs]). These are
    first-order (list scan + kername equality) — no term induction — so lower risk
    than SubstAgree. To do: restate the Lean global-decl types ([GlobalDecl],
    [MutualInductiveBody], [OneInductiveBody], [ConstructorBody], [ConstantBody]) and
    their translation [TEnv] to [EAst.global_declarations], then prove
    [envLookup ↔ lookup_env], [constructorArity ↔ cstr_arity], and
    [isPropositionalInductive ↔ (fst <$> inductive_isprop_and_pars)]. Feeds the
    δ/ι/proj/construct cases of Backward/Forward. *)
