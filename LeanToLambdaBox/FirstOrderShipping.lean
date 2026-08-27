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

* **β+ζ+δ+ctor, plus `Nat` literals in peano mode** (the L3/L4 guard below) and
  recursive constants (through `RecEnvConsistent`, recursion wall W2); `hnfv` still
  pins the subject *outside* any block. The ι (`casesOn`/recursor) variant lives in
  `FirstOrderShippingIota.lean` (`shipping_erase_correct_firstorderι`), over
  `SEvalDataι`: the general ι simulation was once *false* against the un-pinned
  `Erases.cases` (it under-constrained the minor arities), and the arity pins
  (`hpre`/`hnfs`+`hnlen`/`harity`) are what unblocked it.
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
    {known : Name → Prop} {Γ : ErasureCtx} {cfg₀ : ErasureConfig}
    {Esrc Esrcδ : SEnv} {E : GlobalDeclarations}
    (hcon : SEnvConsistent env Us Esrc)
    (hdelta : ErasesEnvDeltaData env Us Γ Esrc E)
    (hctorenv : ErasesEnvCtor Γ E)
    (hcc : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
             Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none)
    (hrec : RecEnvConsistent env Us Γ Esrc E)
    (hnfv : Γ.fixvars = fun _ => none)
    {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw) (P : ProjBridgeHyps Γ gw)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps env Us known Γ cfg₀ Esrcδ gw cc rf)
    (Hβ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      BlockHyps env Us known Γ cfg₀ Esrcδ cc rf)
    (Hreg : RecBlockAgreement env Us known Γ cfg₀)
    {e v : Expr} {ve : VExpr} {t : LBTerm}
    {s s' : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    (hrun : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w')
    (hinv : BridgeInv env Us known Γ cfg₀ (gw w) ctx s [])
    (hsup : Supported known Γ e)
    (htr : TrExprS env Us [] e ve)
    (hnb : NoBlock t)
    (hev : SEvalDataC Γ Esrc e v)
    (hfo : FirstOrderValue env Us Γ [] v) :
    ∃ t', WcbvEval E appliedFlags t t' ∧
      (∃ vve, TrExprS env Us [] v vve) ∧
      Erases env Us Γ [] v t' ∧ NoBlock t' ∧
      ∀ tu, Erases env Us Γ [] v tu → NoBlock tu → tu = t' := by
  obtain ⟨t', vve, heval, htrv, herv, hnbv⟩ :=
    shipping_visitExpr_correct_data henv (Δ := []) trivial hcon hdelta hctorenv hcc hrec
      hnfv H HD C P Hδ Hβ Hreg hrun hinv hsup htr hnb hev
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
    {cfg₀ : ErasureConfig}
    (Hβ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      BlockHyps envFO [] (fun _ => False) ΓFOd cfg₀ (fun _ => none) cc rf)
    (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps envFO [] ΓFOd gw) (HD : DataBridgeHyps ΓFOd gw)
    (C : CasesBridgeHyps ΓFOd gw) (P : ProjBridgeHyps ΓFOd gw)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps envFO [] (fun _ => False) ΓFOd cfg₀ (fun _ => none) gw cc rf)
    (s s' : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld) (t : LBTerm)
    (hrun : Erasure.visitExpr (.const `c []) s ctx cctx ref w = .ok (t, s') w')
    (hinv : BridgeInv envFO [] (fun _ => False) ΓFOd cfg₀ (gw w) ctx s [])
    (hsup : Supported (fun _ => False) ΓFOd (.const `c []))
    (hnb : NoBlock t) :
    ∃ t', WcbvEval EFOd appliedFlags t t' ∧
      (∃ vve, TrExprS envFO [] [] (.const `c []) vve) ∧
      Erases envFO [] ΓFOd [] (.const `c []) t' ∧ NoBlock t' ∧
      ∀ tu, Erases envFO [] ΓFOd [] (.const `c []) tu → NoBlock tu → tu = t' := by
  have heq : (.const `c [] : Expr) = ([] : List Expr).foldl Expr.app (.const `c []) := rfl
  refine shipping_erase_correct_firstorder envFO_wf (Us := []) (Esrc := fun _ => none)
    (E := EFOd) ?_ ?_ ΓFOd_envctor ?_ (recEnvConsistent_of_noRec (Γ := ΓFOd) rfl) rfl
    H HD C P Hδ Hβ RecBlockAgreement.of_bot hrun hinv hsup envFO_trC hnb ?_
    (envFO_foC_d harity)
  · intro Δ n us body cve h; exact absurd h (by simp)
  · intro Δ n body h; exact absurd h (by simp)
  · intro cn iid cidx hc
    by_cases h : cn = `c
    · subst h; rfl
    · simp [ΓFOd, if_neg h] at hc
  · rw [heq]
    exact .ctor_val ΓFOd_ctorsC ΓFOd_ctorAritiesC (by simp) rfl (fun i h => absurd h (by simp))

/-! ## Non-vacuity guard, the literal fragment (Nat-literals wall, L4)

The end-to-end guard the wall is really about: D3 run on the **raw literal node** `2`,
in peano mode. Everything the literal fragment contributes is *constructed* — the
`Supported.natLit` derivation, the `BridgeInv` (its `natcfg` field pinning the run's
config), the source translation (`trExprS_natLit`, at the three-axiom `envNatT` where
`Nat`'s constructors are declared and typed), the source evaluation
(`sevalDataC_natLit`), the arity link (`erasesEnvCtor_natLit`) and the value's
first-orderness. Hypothetical: the run and the three trust bundles (opaque primitives),
`NoBlock t` (a statement about the run's output), and the single lean4lean-blocked side
condition `harity` — *exactly* the one `FirstOrder.lean`'s `envFO` guard carries, for the
same reason (`.const`-vs-arity defeq injectivity is not exposed by the pinned lean4lean).

Note the scope, and do not over-read it: this covers the `Expr.lit` node itself. A
*source-level numeral* `(5 : Nat)` elaborates to `@OfNat.ofNat Nat (lit 5) (instOfNatNat
(lit 5))`, whose `OfNat.ofNat` body erases to an `LBTerm.proj` — and `Erases` is
projection-free by design, so the numeral does not δ-unfold in the model. Raw literals —
what `csimp`, matcher expansion and `Nat`-internals produce — are what this covers.
[Justification corrected at the `fee3ada` re-pin, 2026-08-27: the parenthetical used to
read "(lean4lean's `TrProj` is a `sorry`)", giving the upstream gap as the reason. That
gap is closed; `Erases`'s projection-freeness is now purely our own scope decision
(`Supported` has no `.proj` rule). The scope claim itself is unchanged.] -/

/-- `Nat : Sort 1` at `envNatT`. -/
theorem envNatT_NatTypeSort1 :
    envNatT.HasType 0 [] (.const ``Nat []) (.sort (.succ .zero)) :=
  VEnv.IsDefEq.constDF (env := envNatT) (uvars := 0) (Γ := []) (c := ``Nat)
    (ci := ⟨0, .sort (.succ .zero)⟩) (ls := []) (ls' := []) envNatT_Nat
    (by simp) (by simp) (by simp) (by simp)

/-- The not-a-`Prop` half of informativeness for `Nat`, discharged exactly as
`envFO_notProp` is: `Nat : Sort 1`, so it is not typed by `Sort 0`. -/
theorem envNatT_natNotProp : ¬ envNatT.HasType 0 [] (.const ``Nat []) (.sort .zero) := by
  intro h
  have huniq : envNatT.IsDefEqU 0 [] (.sort .zero) (.sort (.succ .zero)) :=
    VEnv.IsDefEq.uniqU envNatT_wf trivial h envNatT_NatTypeSort1
  have := VEnv.IsDefEqU.sort_inv envNatT_wf trivial huniq
  rw [VLevel.equiv_def] at this; have := this []; simp [VLevel.eval] at this

/-- Every rung of the source tower has informative type `Nat`, modulo the blocked arity
side condition (as in `envFO_informativeC`). -/
theorem informativeType_srcNatTower (harity : ¬ IsArityUpTo envNatT 0 [] (.const ``Nat []))
    (n : Nat) : InformativeType envNatT [] [] (srcNatTower n) :=
  ⟨vNatTower n, .const ``Nat [], trExprS_srcNatTower n, envNatT_towerType n,
    envNatT_natNotProp, harity⟩

/-- The source tower is a `FirstOrderValue`: a saturated constructor spine all the way
down, each rung of informative type. -/
theorem firstOrderValue_srcNatTower
    (harity : ¬ IsArityUpTo envNatT 0 [] (.const ``Nat [])) :
    ∀ n : Nat, FirstOrderValue envNatT [] ΓnatLit [] (srcNatTower n)
  | 0 =>
      .ctor (args := []) ``Nat.zero [] natLitInd 0 ΓnatLit_zero rfl
        (informativeType_srcNatTower harity 0) (fun i h => absurd h (by simp))
  | n + 1 =>
      .ctor (args := [srcNatTower n]) ``Nat.succ [] natLitInd 1 ΓnatLit_succ rfl
        (informativeType_srcNatTower harity (n + 1))
        (fun i h => by
          obtain rfl : i = 0 := by simpa using h
          exact firstOrderValue_srcNatTower harity n)

/-- **D3 fires on a literal.** The shipping eraser, run on `.lit (.natVal 2)` at the
empty state and a peano config, produces a `t` that `WcbvEval`-uates to **the** unique
applied-form erasure of the source value `Nat.succ (Nat.succ Nat.zero)`. -/
example (harity : ¬ IsArityUpTo envNatT 0 [] (.const ``Nat []))
    (cfg : ErasureConfig) (hcfg : cfg.nat = .peano)
    (Hβ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      BlockHyps envNatT [] (fun _ => False) ΓnatLit cfg (fun _ => none) cc rf)
    (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps envNatT [] ΓnatLit gw) (HD : DataBridgeHyps ΓnatLit gw)
    (C : CasesBridgeHyps ΓnatLit gw) (P : ProjBridgeHyps ΓnatLit gw)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps envNatT [] (fun _ => False) ΓnatLit cfg (fun _ => none) gw cc rf)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w w' : Void IO.RealWorld) (t : LBTerm) (s' : ErasureState)
    (hrun : Erasure.visitExpr (.lit (.natVal 2)) {} ⟨{}, none, [], cfg⟩ cctx ref w
      = .ok (t, s') w')
    (hnb : NoBlock t) :
    ∃ t', WcbvEval EnatLit appliedFlags t t' ∧
      (∃ vve, TrExprS envNatT [] [] (srcNatTower 2) vve) ∧
      Erases envNatT [] ΓnatLit [] (srcNatTower 2) t' ∧ NoBlock t' ∧
      ∀ tu, Erases envNatT [] ΓnatLit [] (srcNatTower 2) tu → NoBlock tu → tu = t' := by
  have hinv : BridgeInv envNatT [] (fun _ => False) ΓnatLit cfg (gw w)
      ⟨{}, none, [], cfg⟩ {} [] :=
    { mlc := ⟨.nil, trivial, rfl, rfl⟩
      lparams := rfl
      cfg := rfl
      natcfg := fun _ => hcfg
      kfresh := fun _ h => nomatch h
      fixvars := by intro nm x; simp [ΓnatLit]
      fixfresh := by intro nm x hx; simp [ΓnatLit] at hx
      reserved := fun _ h => nomatch h
      knames := fun _ => rfl
      consts := by intro n k hk; simp at hk }
  refine shipping_erase_correct_firstorder envNatT_wf (Us := []) (Esrc := fun _ => none)
    (E := EnatLit) ?_ ?_ erasesEnvCtor_natLit (fun _ => rfl)
    (recEnvConsistent_of_noRec (Γ := ΓnatLit) rfl) rfl
    H HD C P Hδ Hβ RecBlockAgreement.of_bot hrun hinv
    (.natLit 2 (by simp [ΓnatLit]) ΓnatLit_zero ΓnatLit_succ)
    (trExprS_natLit 2) hnb (sevalDataC_natLit 2) (firstOrderValue_srcNatTower harity 2)
  · intro Δ n us body cve h; exact absurd h (by simp)
  · intro Δ n body h; exact absurd h (by simp)

end LeanToLambdaBox
