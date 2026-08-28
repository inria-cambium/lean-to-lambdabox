import LeanToLambdaBox.ErasureRun
import LeanToLambdaBox.ErasureContext
import Lean4Lean.Verify.NameGenerator
import Lean4Lean.Verify.Axioms

/-!
# The projection-fragment trust bundle: `ProjBridgeHyps`

This structure sits *beside* `BridgeHyps` (`VisitExprRefines.lean`),
`DataBridgeHyps` (`DataBridgeHyps.lean`) and `CasesBridgeHyps`
(`CasesBridgeHyps.lean`), and carries the Hoare-style specifications the
`visitExpr`→`Erases` bridge needs to cover **structure projections**
(`Supported.proj`, `Bridge.lean`) — the projection round's extension of the bridge
to the typeclass-dispatch layer (design slice P8).

It is a *fourth* bundle rather than two extra fields on `CasesBridgeHyps` for the
reason `CasesBridgeHyps` gives for itself: the β+δ+ctor+ι stack's premise set stays
pinned, and every theorem stated against the existing three keeps its exact meaning.

The whole emitter it specifies is six lines (`Erasure.visitProj`):

```lean
  def visitProj (s : Name) (i : Nat) (e : Expr) : EraseM LBTerm := do
    let .inductInfo indinfo ← getConstInfo s | unreachable!
    let (indid, argmasks) ← register_inductive indinfo
    let fieldIdx := argmasks[0]![:i].toArray.count .keep
    let projinfo : ProjectionInfo := { indType := indid, paramCount := indinfo.numParams, fieldIdx }
    return .proj projinfo (← visitExpr e)
```

so **two clauses** suffice, one per non-recursive call, and they pin all three
fields of the emitted `ProjectionInfo`: `indType` and the argmask come from
`register_inductive`'s return, `paramCount` from the fetched `InductiveVal`, and
`fieldIdx` from the argmask through `count_keep_take_replicate` below.

* `projind_run` — `getConstInfo S` on a registered structure returns its
  `inductInfo`, whose `numParams` matches `Γ.projs`. Monotone;
  state-preservation is the *theorem* `Erasure.run_getConstInfo_state`, not an
  assumption. The exact analogue of `CasesBridgeHyps.casesind_run`, one name
  computation lighter: `Expr.proj S i e` already names the structure type, so
  there is no `con.getPrefix`.
* `projreg_run` — `register_inductive` on that inductive returns `Γ`'s
  `InductiveId` and **one** argmask, of the declared field width and trivial.
  The single mask is `register_inductive`'s own `is_struct` gate
  (`inf.ctors.length == 1`), which `Γ.ctorFields iid = some [nf]` expresses in data
  `Γ` already carries; triviality is the same data-fragment assumption
  `DataBridgeHyps.reg_run` / `CasesBridgeHyps.casesreg_run` make (relevant fields,
  the shipping default `remove_irrel_constr_args := false`). No state clause — the
  true state effect is the theorem `Erasure.run_register_inductive_runConcl`.

**No `ProjInfoAgrees`.** There is no analogue of `CasesInfoAgrees`, because
`visitProj` reads no `CasesInfo` and takes no shape decision; and no `inferType`
clause, because the projection path never η-expands. So nothing here is of
`BridgeHyps.orc_run`'s elaborator-correctness class.

**Trust ledger.** Both clauses are Γ↔environment *registration* agreements,
discharged in practice by the same DAG cold-start that discharges
`RegisteredCases`/`RegisteredCtors`/`RegisteredProjs` (`EnvErasureNonrec.lean`), and
both are `env`/`Us`-free: **the projection bridge adds no typing assumption.**

Since slice P9 that cold start is not a plan but a theorem: `RegInvShape`
(`ColdStartShape.lean`) carries a `Γ.projs`-keyed column along the walk, and the ι
cold-start capstone derives `ErasesEnvProjs` and `ProjFieldsCoherent` from it rather
than assuming them. This bundle is what stays: the run-keyed half of the same
agreement, at the two calls `visitProj` makes. Note the split — the registry
invariant answers "the block is registered, and its data is `Γ`'s", this bundle
answers "*this call* returned it".
Because they quantify over opaque runtime primitives their global satisfiability is
not in-logic decidable — the documented trust boundary, exactly as for the other
three bundles. The arithmetic auxiliary `count_keep_take_replicate` *is* checked
non-vacuous here, by computation.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

/-- `ConstructorArgRelevance`'s *derived* `BEq` is reflexive at `keep`. Spelled out
because the enum derives `BEq` but not `LawfulBEq` (shipping code, byte-unchanged),
so the `List.count` lemmas that assume lawfulness are unavailable. -/
theorem keep_beq_self :
    (ConstructorArgRelevance.keep == ConstructorArgRelevance.keep) = true := rfl

/-- A trivial mask of width `i` has `i` retained fields. -/
theorem count_keep_replicate : ∀ (i : Nat),
    (List.replicate i ConstructorArgRelevance.keep).count ConstructorArgRelevance.keep = i
  | 0 => rfl
  | i + 1 => by
      rw [List.replicate_succ, List.count_cons, keep_beq_self, count_keep_replicate i]
      simp

/-- **The field index the model uses is the one the eraser computes**, at a trivial
argmask. `visitProj` takes the mask's `i`-prefix and counts its `keep`s
(`argmasks[0]![:i].toArray.count .keep`); when the mask is `Array.replicate n .keep`
and `i ≤ n` that count is `i`, which is what makes `Erases.proj`'s `fieldIdx := i`
the eraser's own field index rather than an approximation of it.

This is where the all-`keep`-argmask restriction — inherited from `Erases.ctor`, and
now load-bearing in a second place — is cashed in on the bridge side. -/
theorem count_keep_take_replicate {n i : Nat} (h : i ≤ n) :
    ((Array.replicate n ConstructorArgRelevance.keep)[:i]).toArray.count .keep = i := by
  rw [← Array.count_toList]
  have hlist : ((Array.replicate n ConstructorArgRelevance.keep)[:i]).toArray.toList
      = (Array.replicate n ConstructorArgRelevance.keep).toList.take i := by
    rw [← Subarray.toArray_toList]
    simp only [Subarray.toList_eq]
    simp
  rw [hlist, Array.toList_replicate, List.take_replicate, Nat.min_eq_left h,
    count_keep_replicate]

/-- The projection-fragment trust bundle (see module docstring). -/
structure ProjBridgeHyps (Γ : ErasureCtx) (gw : Void IO.RealWorld → NameGenerator) : Prop where
  /-- `getConstInfo S` on a registered structure returns its `inductInfo`, whose
  `numParams` matches `Γ.projs`. Monotone (state-preservation is the theorem
  `Erasure.run_getConstInfo_state`). -/
  projind_run : ∀ (S : Name) (iid : InductiveId) (np : Nat)
    (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (ci : ConstantInfo)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Γ.projs S = some (iid, np) →
    (getConstInfo S : EraseM ConstantInfo) s ctx cctx ref w = .ok (ci, s₁) w₁ →
    gw w ≤ gw w₁ ∧
      ∃ indVal : InductiveVal, ci = .inductInfo indVal ∧ indVal.numParams = np ∧
        indVal.name = S
  /-- `register_inductive` on that inductive returns `Γ`'s `InductiveId` and **one**
  **trivial** argmask — the structure's single constructor's — of the declared field
  width.

  **No state clause** — the `s = s₁` the sibling bundles used to assert is false
  about the real `register_inductive` (`DataBridgeHyps`' module docstring); the
  bridge threads `Erasure.run_register_inductive_runConcl` instead. -/
  projreg_run : ∀ (indVal : InductiveVal) (S : Name) (iid : InductiveId) (np nf : Nat)
    (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld)
    (r : InductiveId × InductiveArgMasks) (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Γ.projs S = some (iid, np) → Γ.ctorFields iid = some [nf] → indVal.name = S →
    register_inductive indVal s ctx cctx ref w = .ok (r, s₁) w₁ →
    gw w ≤ gw w₁ ∧ r.1 = iid ∧ r.2.length = 1 ∧
      r.2[0]! = Array.replicate nf ConstructorArgRelevance.keep

/-- **A projection-free `Γ` satisfies the bundle outright.** Both clauses are keyed on
`Γ.projs S = some _`, which at the default `fun _ => none` is uninhabited, so the
bundle is a *theorem* at every context predating the round rather than a new
assumption on it. That is what keeps the round's cost at zero for the existing
consumers: they thread `P` exactly as they thread the other three bundles, and at
their `Γ` it is derivable rather than assumed.

[Corrected in the coherence pass, 2026-08-27: this docstring used to say "the
`of_bot`-style instance every pre-projection call site uses … they instantiate it,
they do not assume it". Measured, that is false — `of_bot` is applied at exactly one
site, the guard below; every consumer takes `(P : ProjBridgeHyps …)` as a hypothesis,
including the guards at the concrete pre-projection contexts. What is true, and what
the round actually bought, is **derivability** at those contexts, not inlining at
them.] -/
theorem ProjBridgeHyps.of_bot {Γ : ErasureCtx} {gw : Void IO.RealWorld → NameGenerator}
    (h : Γ.projs = fun _ => none) : ProjBridgeHyps Γ gw where
  projind_run := by intro S _ _ _ _ _ _ _ _ _ _ hS; rw [h] at hS; exact absurd hS (by simp)
  projreg_run := by intro _ S _ _ _ _ _ _ _ _ _ _ _ hS; rw [h] at hS; exact absurd hS (by simp)

/-! ## Non-vacuity guards

`ProjBridgeHyps` itself quantifies over opaque runtime primitives, so it cannot be
constructed in-logic at a *registering* `Γ` — that is the documented trust boundary,
as for the other three bundles (the bridge's guards instantiate every other premise
instead, `VisitExprRefines.lean`). What is checked here is the arithmetic auxiliary,
by computation, and the `of_bot` instance. -/

/-- `count_keep_take_replicate` at a **proper** prefix of a three-field mask: the
count is the *index*, not the mask width — so the lemma is not the degenerate
`count = n` in disguise, and `visitProj`'s `fieldIdx` really does track `i`. -/
example : ((Array.replicate 3 ConstructorArgRelevance.keep)[:2]).toArray.count .keep = 2 ∧
    (2 : Nat) ≠ 3 :=
  ⟨count_keep_take_replicate (by omega), by omega⟩

/-- The default `Γ` satisfies the bundle, at any ghost measure. -/
example (gw : Void IO.RealWorld → NameGenerator) :
    ProjBridgeHyps (⟨fun _ => none, fun _ => ⟨.MPfile [], "x"⟩, fun _ => none,
      fun _ => none, fun _ => none, fun _ => none, fun _ => none, false, fun _ => none,
      fun _ => none, fun _ => none, fun _ => []⟩ : ErasureCtx) gw :=
  ProjBridgeHyps.of_bot rfl

end LeanToLambdaBox
