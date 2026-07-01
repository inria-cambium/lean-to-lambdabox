import LeanToLambdaBox.Basic

/-!
# `WcbvFlags` — evaluation flags for λ□

Faithful translation of MetaCoq's `EWcbvEval.WcbvFlags`
(`MetaCoq.Erasure.EWcbvEval`). The weak call-by-value evaluation of λ□ is
parameterised by three booleans:

* `with_prop_case`  — enable the propositional-case reduction rules
  (`iota_sing`, `proj_prop`): a case/projection on an erased proof reduces by
  substituting `□`. MetaCoq's default has this **on**; the `optimize` pass
  removes such cases and targets the **off** semantics.
* `with_guarded_fix` — a `fix` unfolds only once its principal argument is a
  constructor value (the "guarded" recursion of Coq/Lean). With the flag off,
  a `fix` unfolds on any value argument (the malfunction target).
* `with_constructor_as_block` — whether constructors carry their arguments
  *inside* the node (`true`, "block" form) or accumulate them by application
  (`false`). **We are always block form** because `LBTerm.construct` holds its
  args inside and the `Erases` relation only ever produces saturated
  constructors; so we pin this to `true` and do not model the accumulation
  rules (MetaCoq's `eval_construct`/partial-constructor `app_cong`), which are
  unrepresentable in our syntax.

MetaCoq's instances:
```
default_wcbv_flags := { prop_case := true;  guarded_fix := true;  block := false }
opt_wcbv_flags     := { prop_case := false; guarded_fix := true;  block := false }
target_wcbv_flags  := { prop_case := false; guarded_fix := false; block := false }
```
We mirror them with `block := true` (the syntactic deviation justified above).
-/

namespace LeanToLambdaBox

/-- Evaluation flags — MetaCoq `EWcbvEval.WcbvFlags`. -/
structure WcbvFlags where
  with_prop_case            : Bool
  with_guarded_fix          : Bool
  /-- Pinned `true` in this development: `LBTerm.construct` is args-inside. -/
  with_constructor_as_block : Bool
  deriving Repr, DecidableEq

/-- MetaCoq `default_wcbv_flags` — prop-case on, guarded fix. The semantics the
    erasure correctness result targets. -/
def defaultFlags : WcbvFlags := ⟨true, true, true⟩

/-- MetaCoq `opt_wcbv_flags` — prop-case off, guarded fix. The target of the
    `optimize` pass (`LBOptimize`). -/
def optFlags : WcbvFlags := ⟨false, true, true⟩

/-- MetaCoq `target_wcbv_flags` — prop-case off, unguarded fix. The malfunction
    backend target. -/
def targetFlags : WcbvFlags := ⟨false, false, true⟩

/-- Non-block (applied) constructors, prop-case off, guarded fix. This is the form
    the shipping `visitExpr` emits (constructors applied via `.app`); the
    `construct_app` rule of `WcbvEval` is enabled here. -/
def appliedFlags : WcbvFlags := ⟨false, true, false⟩

end LeanToLambdaBox
