import LeanToLambdaBox.Semantics.Substitution

/-!
# Operational semantics for λ□ — aggregator (compatibility shim)

The semantics model lives under `LeanToLambdaBox/Semantics/`:

* `Semantics/Substitution.lean` — `envLookup` + the de Bruijn shift/subst kit.
* `Semantics/Env.lean`          — inductive-metadata queries (`isPropositionalInductive`, …).
* `Semantics/Flags.lean`        — `WcbvFlags` (MetaCoq's `WcbvFlags`).
* `Semantics/Values.lean`       — faithful `atomValue`/`Value` (MetaCoq's `atom`/`value`).
* `Semantics/Eval.lean`         — the canonical big-step `WcbvEval` (MetaCoq's `eval`).
* `Semantics/Metatheory.lean`   — determinism, `eval_to_value`, `value_final`, …

This file re-exports the substitution kit so that `import LeanToLambdaBox.Semantics`
keeps working for consumers that only need it.
-/
