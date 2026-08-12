import LeanToLambdaBox.VisitExprRefines
import LeanToLambdaBox.OracleDischarge
import LeanToLambdaBox.ErasesCorrect

/-!
# The top-level theorem: the shipping erasure is semantically correct

This composes the two halves of the verification:

* **the bridge** (`visitExpr_refines_erases`, `VisitExprRefines.lean`): a
  successful run of the *shipping* `Erasure.visitExpr` produces an `LBTerm`
  related to the source by the typed erasure relation `Erases` — proved by
  fixpoint induction over the (de-partialized) implementation itself;
* **the simulation** (`erases_correct`, `ErasesCorrect.lean`): `Erases`
  forward-simulates source evaluation (β + δ fragment) into the λ□ semantics.

The conclusion is that of `erases_correct` — and of `eraseCore_correct`, the
pure-model predecessor this theorem supersedes as the statement about the real
transpiler: the erased program `Eval`-uates to an erasure of the source value.

## Trust boundary (each premise, honestly)

* `henv`/`htr` (+ `hΔ`): lean4lean's model of the kernel — the environment
  translates (`VEnv.WF`) and the source term is well-typed as witnessed by a
  translation `TrExprS`. These are exactly what lean4lean's `TrEnv`/
  `VContext.mk'` machinery provides for kernel-accepted input; producing them
  for a *concrete* `Lean.Environment` is lean4lean's own trust boundary
  (`PROJECT_STATUS_HANDOFF.md`, Task C), stated here as premises — not
  axiomatized away.
* `H : BridgeHyps`: Hoare-style specs of the four opaque runtime primitives the
  supported fragment exercises (the relevance oracle, `mkFreshFVarId`,
  `getCasesInfo?`, `getCtorArity?`), relative to a ghost name-generator measure
  `gw`. **The oracle's kernel path is now discharged, not assumed**
  (`shipping_visitExpr_correct'` below): its soundness is *proved* from
  `isErasable.WF` via the generalized run-adequacy `M.WF.run'`
  (`CheckerAdequacy.lean`, `kernel_isErasable_sound`), leaving as trust only the
  reflection of impure `CoreM`/`MetaM` plumbing onto the pure `M.run` and the
  `isErasableMeta` fallback (packaged as `ResidualHyps`, `OracleDischarge.lean`).
  The `BridgeHyps`-taking `shipping_visitExpr_correct` is retained as the raw form.
* `hcon`/`hdelta`: source-env ↔ `VEnv` ↔ target-env consistency, as in
  `erases_correct`.
* `hinv`/`hsup`: the run starts in a state corresponding to `Δ`/`Γ` with all
  `known` constants pre-registered, and the source lies in the supported v1
  fragment (`Supported`, `Bridge.lean`) — `box|bvar|fvar|const|app|lam|letE`,
  constructor/`casesOn`/literal/`mdata`/projection-free.

Everything else — the de Bruijn↔fvar reconciliation, the traversal, the state
and name-generator bookkeeping, the relation to the semantics — is proved.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

/--
**The shipping term-level eraser is semantically correct** on the supported
fragment (β + δ): if the real `Erasure.visitExpr` succeeds on `e` producing
`t`, and the source `e` `SEvalβδ`-evaluates to a value `v`, then `t`
`Eval`-uates to an erasure of `v`.

This is the "single top-level *the shipping erase is correct* theorem" the
handoff asked to conclude, with `eraseCore` replaced by the real
implementation (see the module docstring for why the pure-model route was
impossible). Environment-level erasure (`visitMutual`/`fix`) and the
constructor/`casesOn` fragment remain future work, exactly as scoped in
`Bridge.lean`.
-/
theorem shipping_visitExpr_correct
    {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ)
    {known : Name → Prop} {Γ : ErasureCtx} {Esrc : SEnv} {E : GlobalDeclarations}
    (hcon : SEnvConsistent env Us Esrc)
    (hdelta : ErasesEnvDelta env Us Γ Esrc E)
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
    (hev : SEvalβδ Esrc e v) :
    ∃ t' vve, Eval E t t' ∧ TrExprS env Us Δ v vve ∧ Erases env Us Γ Δ v t' :=
  erases_correct henv hΔ hcon hdelta hrec hnfv htr
    (visitExpr_refines_erases H HD C henv.ordered e s ctx cctx ref w t s' w' hrun
      Δ hinv hsup ⟨ve, htr⟩).1
    hev

/--
**The shipping term-level eraser is correct, with the relevance oracle's kernel
path discharged.** Same conclusion as `shipping_visitExpr_correct`, but the oracle
soundness is no longer a raw assumption: it is supplied via `ResidualHyps` (whose
kernel branch is *proved* through `kernel_isErasable_sound`) together with the
lean4lean environment model `ves.WF env₀`. This is the theorem in which the
previous batch's verified relevance check (`isErasable.WF`) becomes *load-bearing*
inside the top-level correctness statement, rather than a result sitting beside it.

The residual oracle trust is now exactly: (i) the reflection of the impure
`CoreM`/`MetaM` oracle run onto the pure `M.run` of the verified checker, and
(ii) the `isErasableMeta` fallback's soundness — both packaged in `ResidualHyps`
(`OracleDischarge.lean`); everything else about relevance is proved.
-/
theorem shipping_visitExpr_correct'
    {env₀ : Lean.Kernel.Environment} {ves : Lean4Lean.VEnvs} (wf : ves.WF env₀)
    {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF (ves.venv .safe) Us.length Δ)
    {known : Name → Prop} {Γ : ErasureCtx} {Esrc : SEnv} {E : GlobalDeclarations}
    (hcon : SEnvConsistent (ves.venv .safe) Us Esrc)
    (hdelta : ErasesEnvDelta (ves.venv .safe) Us Γ Esrc E)
    (hrec : RecEnvConsistent (ves.venv .safe) Us Γ Esrc E)
    (hnfv : Γ.fixvars = fun _ => none)
    {gw : Void IO.RealWorld → NameGenerator}
    (R : ResidualHyps env₀ ves Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
    {e v : Expr} {ve : VExpr} {t : LBTerm}
    {s s' : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    (hrun : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w')
    (hinv : BridgeInv (ves.venv .safe) Us known Γ (gw w) ctx s Δ)
    (hsup : Supported known Γ e)
    (htr : TrExprS (ves.venv .safe) Us Δ e ve)
    (hev : SEvalβδ Esrc e v) :
    ∃ t' vve, Eval E t t' ∧ TrExprS (ves.venv .safe) Us Δ v vve ∧
      Erases (ves.venv .safe) Us Γ Δ v t' :=
  shipping_visitExpr_correct wf.tr.wf hΔ hcon hdelta hrec hnfv (R.toBridgeHyps wf) HD C
    hrun hinv hsup htr hev

/-! ## Non-vacuity guard

The logical premises are jointly satisfiable and the theorem fires. As in
`VisitExprRefines.lean`'s guard, the run equation and `BridgeHyps` — statements
about *opaque* runtime primitives, whose truth is not in-logic decidable — are
taken as inputs (the documented trust boundary); everything else is
**constructed**: the empty (well-formed) `VEnv`, the empty source environment
(making both consistency premises vacuously true), a concrete well-typed,
supported source term `fun (a : Sort 0) => a` that `SEvalβδ`-evaluates (to
itself, as a value), its `TrExprS` witness, and a concrete `BridgeInv` at
`Δ = []`. -/
example (Γ : ErasureCtx) (hΓrec : Γ.recBodies = fun _ => none)
    (hΓfv : Γ.fixvars = fun _ => none)
    (hkn : ∀ n : Name, Γ.constants n = toKername n) (cfg : ErasureConfig)
    (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps .empty [] Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w w' : Void IO.RealWorld) (t : LBTerm) (s' : ErasureState)
    (hrun : Erasure.visitExpr (.lam `a (.sort .zero) (.bvar 0) .default) {}
      ⟨{}, none, [], cfg⟩ cctx ref w = .ok (t, s') w') :
    ∃ t' vve, Eval ([] : GlobalDeclarations) t t' ∧
      TrExprS .empty [] [] (.lam `a (.sort .zero) (.bvar 0) .default) vve ∧
      Erases .empty [] Γ [] (.lam `a (.sort .zero) (.bvar 0) .default) t' := by
  have henv : VEnv.WF .empty := ⟨[], .empty⟩
  have hty : TrExprS .empty [] [] (.sort .zero) (.sort .zero) := .sort rfl
  have hfind : Lean4Lean.VLCtx.find?
      [(none, Lean4Lean.VLocalDecl.vlam (.sort .zero))] (.inl 0)
      = some (.bvar 0, (VExpr.sort .zero).lift) := by
    simp [Lean4Lean.VLCtx.find?, Lean4Lean.VLCtx.next,
      Lean4Lean.VLocalDecl.value, Lean4Lean.VLocalDecl.type]
  have hbody : TrExprS .empty [] [(none, .vlam (.sort .zero))] (.bvar 0) (.bvar 0) :=
    .bvar hfind
  have htr : TrExprS .empty [] [] (.lam `a (.sort .zero) (.bvar 0) .default)
      (.lam (.sort .zero) (.bvar 0)) :=
    .lam ⟨_, .sortDF trivial trivial rfl⟩ hty hbody
  exact shipping_visitExpr_correct (Esrc := fun _ => none) henv
    (Lean4Lean.TrLCtx.nil (env := .empty) (Us := [])).wf
    (fun h _ => nomatch h) (fun h => nomatch h)
    (recEnvConsistent_of_noRec (Γ := Γ) hΓrec) hΓfv
    H HD C (known := fun _ => False) hrun
    { mlc := ⟨.nil, trivial, rfl, rfl⟩
      lparams := rfl
      kfresh := fun _ h => nomatch h
      fixvars := rfl
      reserved := fun _ h => nomatch h
      knames := hkn
      consts := by intro n k hk; simp at hk
      known_dom := fun _ h => h.elim }
    (.lam _ _ _ (.bvar 0)) htr (.lam `a (.sort .zero) (.bvar 0) .default)

end LeanToLambdaBox
