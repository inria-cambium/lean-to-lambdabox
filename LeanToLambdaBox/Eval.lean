import LeanToLambdaBox.Semantics.Eval

/-!
# Big-step λ□ evaluation — compatibility shim

The big-step semantics now lives in `LeanToLambdaBox/Semantics/Eval.lean` as the
faithful, flag-parameterised `WcbvEval` (MetaCoq's `EWcbvEval.eval`), with `Eval`
and `EvalProp` recovered as `abbrev`s (`WcbvEval Γ optFlags` / `WcbvEval Γ
defaultFlags`). This file re-exports it so `import LeanToLambdaBox.Eval` keeps
working for existing consumers (`ErasesCorrect`, `Optimize`).
-/
