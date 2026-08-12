import LeanToLambdaBox.VisitExprRefines
import LeanToLambdaBox.ErasesCorrectData
import LeanToLambdaBox.FirstOrder

/-!
# The shipping eraser is correct on the data fragment (A9/C5)

Composes the **widened bridge** (`visitExpr_refines_erases`, now covering
`Supported.ctorApp` — saturated first-order constructors, A8) with the
**data-fragment forward simulation** (`erases_correct_data`, β + δ + saturated
constructors, at MetaRocq's non-block `appliedFlags`, WS-F). The result: a
successful run of the *shipping* `Erasure.visitExpr` on a supported source term
`e` that `SEvalDataC`-evaluates to `v` yields an `LBTerm` `t` whose non-block
`WcbvEval` reaches an erasure of `v`.

## The `NoBlock` premise

`erases_correct_data` requires `NoBlock t` (a nonempty block-constructor node is
stuck at `appliedFlags`). The shipping erasure is *always* applied form — the
constructor path emits `mkApps (.construct iid cidx []) args'` (`ctor_head` +
`Erases.app` spine, never the abstract block `Erases.ctor`) — so `NoBlock t`
holds of every `visitExpr` output. It is threaded as a premise here (a structural
property of the shipping output, discharged concretely in the non-vacuity guard),
exactly as the WS-F brief prescribes.

## Trust boundary

The union of `BridgeHyps` (β+δ oracle/fresh/classifier specs) and `DataBridgeHyps`
(the constructor data-path primitive specs — `getConstInfo`/`register_inductive`/
`getEnv`/`inferType`), plus the WS-F environment-consistency premises
(`SEnvConsistent`/`ErasesEnvDeltaData`/`ErasesEnvCtor`) and lean4lean's model
(`env.WF`, `TrExprS`). Everything else — the traversal, the de Bruijn↔fvar
reconciliation, the constructor spine reconstruction, the semantics — is proved.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

/--
**The shipping term-level eraser is correct on the data fragment** (β + δ +
saturated constructors) at MetaRocq's non-block `appliedFlags`: if the real
`Erasure.visitExpr` succeeds on `e` producing an applied-form (`NoBlock`) `t`, and
`e` `SEvalDataC`-evaluates to `v`, then `t` `WcbvEval`-uates (at `appliedFlags`) to
an applied-form erasure of `v`.

This supersedes `shipping_visitExpr_correct` (β+δ, block `Eval`) with the
constructor-carrying `Supported.ctorApp` fragment and the non-block target.
-/
theorem shipping_visitExpr_correct_data
    {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ)
    {known : Name → Prop} {Γ : ErasureCtx} {Esrc : SEnv} {E : GlobalDeclarations}
    (hcon : SEnvConsistent env Us Esrc)
    (hdelta : ErasesEnvDeltaData env Us Γ Esrc E)
    (hctorenv : ErasesEnvCtor Γ E)
    (hcc : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
             Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none)
    (hrec : RecEnvConsistent env Us Γ Esrc E)
    (hnfv : Γ.fixvars = fun _ => none)
    {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
    {e v : Expr} {ve : VExpr} {t : LBTerm}
    {s s' : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    (hrun : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w')
    (hinv : BridgeInv env Us known Γ (gw w) ctx s Δ)
    (hsup : Supported known Γ e)
    (htr : TrExprS env Us Δ e ve)
    (hnb : NoBlock t)
    (hev : SEvalDataC Γ Esrc e v) :
    ∃ t' vve, WcbvEval E appliedFlags t t' ∧ TrExprS env Us Δ v vve ∧
      Erases env Us Γ Δ v t' ∧ NoBlock t' :=
  erases_correct_data henv hΔ hcon hdelta hctorenv hcc hrec hnfv hev htr
    (visitExpr_refines_erases H HD C henv.ordered e s ctx cctx ref w t s' w' hrun
      Δ hinv hsup ⟨ve, htr⟩).1
    hnb

/-! ## Non-vacuity guard

Reuses the concrete nullary first-order constructor `c : I` of `FirstOrder.lean`
(`envFO`/`ΓFOd`/`EFOd`): the source-env hypotheses hold vacuously (empty `Esrc`),
`ErasesEnvCtor` by `ΓFOd_envctor`, and the source `c` `SEvalDataC`-evaluates to
itself. The run and the two trust bundles stay hypothetical (opaque primitives);
everything else — including the `NoBlock` witness — is constructed. -/
example (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps envFO [] ΓFOd gw) (HD : DataBridgeHyps ΓFOd gw)
    (C : CasesBridgeHyps ΓFOd gw)
    (s s' : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld) (t : LBTerm)
    (hrun : Erasure.visitExpr (.const `c []) s ctx cctx ref w = .ok (t, s') w')
    (hinv : BridgeInv envFO [] (fun _ => False) ΓFOd (gw w) ctx s [])
    (hsup : Supported (fun _ => False) ΓFOd (.const `c []))
    (htr : TrExprS envFO [] [] (.const `c []) (.const `c []))
    (hnb : NoBlock t) :
    ∃ t' vve, WcbvEval EFOd appliedFlags t t' ∧ TrExprS envFO [] [] (.const `c []) vve ∧
      Erases envFO [] ΓFOd [] (.const `c []) t' ∧ NoBlock t' := by
  have heq : (.const `c [] : Expr) = ([] : List Expr).foldl Expr.app (.const `c []) := rfl
  refine shipping_visitExpr_correct_data envFO_wf (Us := []) (Δ := []) trivial
    (Esrc := fun _ => none) (E := EFOd) ?_ ?_ ΓFOd_envctor ?_
    (recEnvConsistent_of_noRec (Γ := ΓFOd) rfl) rfl H HD C hrun hinv hsup htr hnb ?_
  · intro Δ n us body cve h; exact absurd h (by simp)
  · intro Δ n body h; exact absurd h (by simp)
  · intro cn iid cidx hc
    by_cases h : cn = `c
    · subst h; rfl
    · simp [ΓFOd, if_neg h] at hc
  · rw [heq]
    exact .ctor_val ΓFOd_ctorsC ΓFOd_ctorAritiesC (by simp) rfl (fun i h => absurd h (by simp))

end LeanToLambdaBox
