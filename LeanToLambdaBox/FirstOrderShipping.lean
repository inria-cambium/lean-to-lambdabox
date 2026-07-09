import LeanToLambdaBox.ShippingCorrectData
import LeanToLambdaBox.FirstOrder

/-!
# The first-order shipping theorem (D3) — collaborator Q3's capstone

The comment-3 theorem, made precise for the *real* transpiler and the β+δ+ctor
fragment: **if a closed source term `e` erases (via the shipping
`Erasure.visitExpr`) to `t`, and `e` evaluates — validated against lean4lean's
definitional equality by subject reduction — to a *first-order value* `v`, then
the erased program `t` evaluates (`WcbvEval E appliedFlags`) to the *unique*
applied-form erasure of `v`.**

Uniqueness is what makes this a *function*-level statement despite `Erases` being a
relation: on a first-order value the relation collapses to a single applied-form
(`NoBlock`) image (`firstOrder_value_erases_unique`, D1) — the box rule is killed by
informativeness (A2) and the abstract block `ctor` rule by `NoBlock` — so the target
value `t'` this theorem produces is pinned down by `v` alone, independent of the
non-deterministic erasure derivation.

## Scope and the `eraseCore` connection

* **β+δ+ctor only** (as instructed). The ι (`casesOn`/recursor) variant is deferred:
  the general ι forward simulation is *false* against the current `Erases.cases`
  (it under-constrains the minor arities), so it needs `Erases.cases` strengthened
  first (out of scope here).
* The *pure* canonicaliser `eraseCore` (`FirstOrder.firstOrderValue_erases_eq_eraseCore`,
  D2) produces the **block** form `.construct iid cidx args'` (args inside), whereas
  the shipping / `appliedFlags` value `t'` here is the **applied** form
  `mkApps (.construct iid cidx []) args'`. They are the block/non-block images of the
  *same* erasure and are related by MetaRocq's verified `construct_as_block`
  transform; this theorem delivers the applied-form value directly (the one that
  actually evaluates at `appliedFlags`), and its *uniqueness* among applied erasures.

## `NoBlock t`

Threaded as a premise: the shipping erasure of a supported term is always applied
form, so `NoBlock t` holds of every `visitExpr` output (see `ShippingCorrectData`).
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

/--
**D3 — the shipping eraser is correct on first-order results.** For a closed
(`Δ = []`) supported `e` that the shipping `visitExpr` erases to an applied-form
(`NoBlock`) `t`, and that `SEvalDataC`-evaluates to a *first-order value* `v`: the
target `t` `WcbvEval`-uates at `appliedFlags` to `t'`, which is **the** unique
applied-form (`NoBlock`) erasure of `v` (any other applied erasure of `v` equals it).
-/
theorem shipping_erase_correct_firstorder
    {env : VEnv} (henv : env.WF) {Us : List Name}
    {known : Name → Prop} {Γ : ErasureCtx} {Esrc : SEnv} {E : GlobalDeclarations}
    (hcon : SEnvConsistent env Us Esrc)
    (hdelta : ErasesEnvDeltaData env Us Γ Esrc E)
    (hctorenv : ErasesEnvCtor Γ E)
    (hcc : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
             Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none)
    (hnfenv : NoFixEnv E)
    {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw)
    {e v : Expr} {ve : VExpr} {t : LBTerm}
    {s s' : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    (hrun : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w')
    (hinv : BridgeInv env Us known Γ (gw w) ctx s [])
    (hsup : Supported known Γ e)
    (htr : TrExprS env Us [] e ve)
    (hnb : NoBlock t)
    (hnfx : NoFix t)
    (hev : SEvalDataC Γ Esrc e v)
    (hfo : FirstOrderValue env Us Γ [] v) :
    ∃ t', WcbvEval E appliedFlags t t' ∧
      (∃ vve, TrExprS env Us [] v vve) ∧
      Erases env Us Γ [] v t' ∧ NoBlock t' ∧
      ∀ tu, Erases env Us Γ [] v tu → NoBlock tu → tu = t' := by
  obtain ⟨t', vve, heval, htrv, herv, hnbv⟩ :=
    shipping_visitExpr_correct_data henv (Δ := []) trivial hcon hdelta hctorenv hcc hnfenv
      H HD hrun hinv hsup htr hnb hnfx hev
  exact ⟨t', heval, ⟨vve, htrv⟩, herv, hnbv,
    fun tu hertu hnbtu =>
      firstOrder_value_erases_unique henv (Δ := []) trivial hfo hertu hnbtu herv hnbv⟩

/-! ## Non-vacuity guard

The concrete nullary first-order constructor `c : I` (`FirstOrder.lean`): `c`
`SEvalDataC`-evaluates to itself, is a `FirstOrderValue` (modulo the one
lean4lean-blocked arity side condition `harity`, exactly as in `FirstOrder.lean`),
and D3 *fires* — producing `t'` and its uniqueness. The run and the two trust
bundles stay hypothetical (opaque primitives); everything else is constructed. -/
example (harity : ¬ IsArityUpTo envFO 0 [] (.const `I []))
    (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps envFO [] ΓFOd gw) (HD : DataBridgeHyps ΓFOd gw)
    (s s' : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld) (t : LBTerm)
    (hrun : Erasure.visitExpr (.const `c []) s ctx cctx ref w = .ok (t, s') w')
    (hinv : BridgeInv envFO [] (fun _ => True) ΓFOd (gw w) ctx s [])
    (hsup : Supported (fun _ => True) ΓFOd (.const `c []))
    (hnb : NoBlock t) (hnfx : NoFix t) :
    ∃ t', WcbvEval EFOd appliedFlags t t' ∧
      (∃ vve, TrExprS envFO [] [] (.const `c []) vve) ∧
      Erases envFO [] ΓFOd [] (.const `c []) t' ∧ NoBlock t' ∧
      ∀ tu, Erases envFO [] ΓFOd [] (.const `c []) tu → NoBlock tu → tu = t' := by
  have heq : (.const `c [] : Expr) = ([] : List Expr).foldl Expr.app (.const `c []) := rfl
  refine shipping_erase_correct_firstorder envFO_wf (Us := []) (Esrc := fun _ => none)
    (E := EFOd) ?_ ?_ ΓFOd_envctor ?_ ?_ H HD hrun hinv hsup envFO_trC hnb hnfx ?_ (envFO_foC_d harity)
  · intro Δ n us body cve h; exact absurd h (by simp)
  · intro Δ n body h; exact absurd h (by simp)
  · intro cn iid cidx hc
    by_cases h : cn = `c
    · subst h; rfl
    · simp [ΓFOd, if_neg h] at hc
  · intro kn body' h
    simp only [EFOd, LBTerm.envLookup] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  · rw [heq]
    exact .ctor_val ΓFOd_ctorsC ΓFOd_ctorAritiesC (by simp) rfl (fun i h => absurd h (by simp))

end LeanToLambdaBox
