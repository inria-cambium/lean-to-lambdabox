(** * ValuesAgree.v — value/atom agreement (roadmap).

    The restated Lean [Value]/[atomValue]/[isStuckApp] correspond, under [T], to
    MetaRocq [EWcbvEval.value]/[atom]/[value_head] at [with_constructor_as_block =
    false] (the validated target). The non-block constructor and applied-fix values
    are [mkApps]-spines on both sides ([mkApps (tConstruct ind c []) args] /
    [mkApps (tFix mfix i) argsv]), so the correspondence is by spine induction. To
    prove: [T (mkApps h args) = mkApps (T h) (map T args)] (spine commutation),
    [isStuckApp ↔ the negated eval_app_cong side condition] under [T], and
    [Value Γ fl v ↔ value (TEnv Γ) (T v)] (block=false). Feeds the value-final /
    eval_to_value bridging in Forward/Backward. *)
