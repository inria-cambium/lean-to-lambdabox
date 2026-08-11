import LeanToLambdaBox.EnvErasure
import LeanToLambdaBox.ErasesCorrectIota

/-!
# The first-order shipping theorem over `SEvalDataι` (D3ι) — the ι capstone

The ι variant of `shipping_erase_correct_firstorder` (`FirstOrderShipping.lean`): the
same statement, with the source evaluation upgraded from `SEvalDataC` (β + δ + saturated
constructors) to **`SEvalDataι`** (the same, plus the corrected ι), so that first-order
programs which *pattern-match* are covered. Additive throughout — no existing statement
changes.

## The composition

```
 visitExpr_refines_erases      (T4b bridge, `Supported.casesApp` = λ-telescope minors)
   ⟶ Erases env Us Γ [] e t
 erases_correct_dataι          (T3 forward simulation, flat fragment)
   ⟶ WcbvEval E appliedFlags t t'  ∧  Erases … v t' ∧ NoBlock t' ∧ LBClosed t' 0
 firstOrder_value_erases_unique (D1)
   ⟶ t' is *the* applied-form erasure of v
```

Three declarations land here, in the repo's established interface/implementation shape:

* `shipping_erase_correct_firstorderι` — the capstone, taking `IotaConsistent` as the
  **interface** premise (exactly as `SEvalDataι_defeq` does, and for the same reason:
  it keeps the kernel-environment parameters `safety`/`kenv` out of a statement about
  `VEnv`s). Its axiom set is *identical* to the non-ι capstone's.
* `shipping_erase_correct_firstorderι_of_shape` — the same with `IotaConsistent`
  **discharged** by `iotaConsistent_of_shape` from `PatsIotaSpec + SEnvConsistent +
  IotaShape`. This is the honest end-to-end form; it costs eight further lean4lean
  *modelling* axioms (see the trust ledger below), no axiom of ours.
* `shipping_erase_correct_firstorderι_registered` — the ι analogue of
  `shipping_erase_correct_firstorder_registered`: every `Γ`/`E` env-consistency premise
  sourced from the registration records (`RegisteredClosureData`, `RegisteredCtors`,
  `RegisteredCases`, `RegisteredCtorFieldsAll`) instead of assumed.

## The trust ledger for D3ι (which premise is what)

Beyond D3's own bundle, the ι fragment adds nothing that is an axiom. Precisely:

* **Certificates — `rfl`/`decide`-checkable data about a concrete inductive, carrying no
  typing or translation content.** `IotaShape` (kernel lookups plus closed `Expr`
  equations; guards `betaN_casesOn_guard` / `betaN_ruleTemplate_{,eta_,rec_}guard`),
  `IotaArityCoherent`, `CtorFieldsCoherent`, `FlatCaseFields`, `ErasesEnvCases`
  (hence `ErasesEnvCasesι`, via `ErasesEnvCases.nonProp`), `ErasesEnvCtor`, `ClosedEnv`,
  `NoFixEnv`, and the constructor/`casesOn` disjointness `hcc`. In the `_registered`
  form all of the `Γ`/`E` ones are *derived* from the registration records. All of them
  are constructed jointly at one registered inductive in the guard below.
* **Runtime Hoare assumptions — specs about opaque `IO` primitives, the documented
  trust boundary.** `BridgeHyps`, `DataBridgeHyps`, `CasesBridgeHyps` (the last one
  carries `visitCases`' `inferType` spec), plus the run/invariant premises
  `hrun`/`hinv`.
* **`PatsIotaSpec` — the upstream item, now discharged**: the fork's strengthened rule
  lookup. It is *not* an assumption about our code, and no longer an open obligation —
  `PatsIotaSpec.of_trEnv` (`IotaPattern.lean`) builds it from any `TrEnv`. Only the
  `_of_shape` form mentions it.
* **`IotaRelevant` — a model-over-approximation guard**, the ι analogue of `NoBlock`:
  it excludes the two `Erases` derivations the relation permits, the shipping
  `visitCases` never emits, and under which the target `.case` is provably stuck
  (`SubjectReductionIota.lean`). Not a typing assumption.
* **Pre-existing D3 premises, unchanged**: `env.WF`, `SEnvConsistent`,
  `ErasesEnvDeltaData` (or `RegisteredClosureData`), `NoFixEnv E`, `Supported`,
  `TrExprS`, `NoBlock t`, `NoFix t`, `FirstOrderValue`.
* **New relative to D3**: the closedness thread `LBClosed t 0` / `ClosedEnv E`. It is
  MetaRocq's own `closedn 0` convention, not a modelling shortcut — see
  `ErasesCorrectIota.lean` for the two-field counterexample that forces it. The
  conclusion correspondingly *gains* `LBClosed t' 0`.

## Scope: the flat-fields restriction is simulation-side only

`FlatCaseFields Γ` (every constructor of an eliminated inductive retains zero fields —
`Bool`, `Ordering`, enumerations) is inherited from `erases_correct_dataι`, and only from
there. The **bridge is already general**: T4b's `Supported.casesApp` pins each minor to a
manifest λ-telescope of its constructor's field arity and carries no zero-field
condition, and `Supported.casesApp_inv` likewise. Lifting the restriction (S4b) is
therefore a change to the simulation alone: the general β-chain ↔ reversing-`iota_red`
bridge (whose `LBTerm.subst_subst` is already available in `Closed.lean`) plus the
two-stage `IotaShape` (already landed). Nothing here or in `Bridge.lean` moves.

## Non-vacuity

See the guard section at the bottom: the whole `Γ`/`E` certificate block is constructed
at one genuinely registered, non-propositional, flat inductive, and D3ι *fires* there.
The end-to-end guard in which the ι rule itself reduces a real pattern match is **not
constructible at this pin** — the same `VEnv.WF`-unconstructible-for-`pats` obstruction
that already blocks a guard for `iotaConsistent_of_shape` / `SEvalDataι_defeq`
(`VEnv.Ordered` has no `addPat` clause; `addInduct_WF` is `sorry` upstream). It is
recorded at the guard, as `ErasesCorrectIota.lean` does for `IotaRelevant`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

/-! ## D3ι — the capstone -/

/--
**D3ι — the shipping eraser is correct on first-order results of ι programs.** For a
closed (`Δ = []`) supported `e` that the shipping `visitExpr` erases to an applied-form
(`NoBlock`), fix-free, de-Bruijn-closed `t`, and that **`SEvalDataι`**-evaluates (β + δ +
saturated constructors + ι) to a *first-order value* `v`: the target `t` `WcbvEval`-uates
at `appliedFlags` to `t'`, which is **the** unique applied-form erasure of `v`.

Identical to `shipping_erase_correct_firstorder` except that (i) the source evaluation is
`SEvalDataι`, (ii) the ι side conditions of `erases_correct_dataι` are threaded, and
(iii) the closedness thread `LBClosed` runs through hypothesis and conclusion. `Erases`
uniqueness on the value is D1 as before, and is unaffected by ι: it is a statement about
the *value*, which is a first-order constructor spine either way.

`IotaConsistent` is taken as the **interface** premise, mirroring `SEvalDataι_defeq`;
`shipping_erase_correct_firstorderι_of_shape` is the form with it discharged.
`ErasesEnvCasesι` is *not* a premise: it is read off `ErasesEnvCases` by
`ErasesEnvCases.nonProp` — the composition point `ErasesCorrectIota.lean` names.
-/
theorem shipping_erase_correct_firstorderι
    {env : VEnv} (henv : env.WF) {Us : List Name}
    {known : Name → Prop} {Γ : ErasureCtx} {ia : IotaArities}
    {Esrc : SEnv} {E : GlobalDeclarations}
    (hcon : SEnvConsistent env Us Esrc)
    (hiota : IotaConsistent env Us Γ ia)
    (hdelta : ErasesEnvDeltaData env Us Γ Esrc E)
    (hctorenv : ErasesEnvCtor Γ E)
    (hcasesenv : ErasesEnvCases Γ E)
    (hcoh : CtorFieldsCoherent Γ)
    (hiacoh : IotaArityCoherent Γ ia)
    (hflat : FlatCaseFields Γ)
    (hrel : IotaRelevant env Us Γ)
    (hcc : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
             Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none)
    (hnfenv : NoFixEnv E)
    (hclenv : ClosedEnv E)
    {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
    {e v : Expr} {ve : VExpr} {t : LBTerm}
    {s s' : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    (hrun : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w')
    (hinv : BridgeInv env Us known Γ (gw w) ctx s [])
    (hsup : Supported known Γ e)
    (htr : TrExprS env Us [] e ve)
    (hnb : NoBlock t)
    (hnfx : NoFix t)
    (hcl : LBClosed t 0)
    (hev : SEvalDataι Γ ia Esrc e v)
    (hfo : FirstOrderValue env Us Γ [] v) :
    ∃ t', WcbvEval E appliedFlags t t' ∧
      (∃ vve, TrExprS env Us [] v vve) ∧
      Erases env Us Γ [] v t' ∧ NoBlock t' ∧ LBClosed t' 0 ∧
      ∀ tu, Erases env Us Γ [] v tu → NoBlock tu → tu = t' := by
  obtain ⟨t', vve, heval, htrv, herv, hnbv, _, hclv⟩ :=
    erases_correct_dataι henv (Δ := []) trivial hcon hiota hdelta hctorenv
      (fun hc => hcasesenv.nonProp hc) hcoh hiacoh hflat hrel hcc hnfenv hclenv hev htr
      (visitExpr_refines_erases H HD C henv.ordered e s ctx cctx ref w t s' w' hrun
        [] hinv hsup ⟨ve, htr⟩).1
      hnb hnfx hcl
  exact ⟨t', heval, ⟨vve, htrv⟩, herv, hnbv, hclv,
    fun tu hertu hnbtu =>
      firstOrder_value_erases_unique henv (Δ := []) trivial hfo hertu hnbtu herv hnbv⟩

/-- **D3ι with `IotaConsistent` discharged.** The same theorem, with the ι interface
premise replaced by the pair that *derives* it (`iotaConsistent_of_shape`,
`IotaDischarge.lean`): the fork's strengthened rule lookup `PatsIotaSpec`, and the
per-`casesOn` kernel shape certificate `IotaShape`. `SEnvConsistent` — already a premise
— is the third input, which is why the δ step of the ι chain does **not** route through
`TrEnv.of_value` and therefore does not inherit the `Aligned.addInduct` `sorry` that
taints that route at the current pin.

This is the form to quote when asking "what does the ι capstone assume": everything is
either a `rfl`-checkable certificate, a documented runtime Hoare spec, or `PatsIotaSpec`
(discharged by `PatsIotaSpec.of_trEnv`). The price is eight further lean4lean **modelling**
axioms, inherited from `TrExprS.instL` (level-instantiating a polymorphic recursor rule):
`Lean.Expr.mkData_eq`, `Lean.Expr.mkAppData_eq`, `Lean.Expr.replace_eq`,
`Lean.Level.hasMVar_eq`, `Lean.Level.hasParam_eq`, `Lean.Level.instLawfulBEqLevel`, and
lean4lean's two `bv_decide` native checks in its own `Expr.Data` bit-packing proofs.
They are **not new**: the set is a strict subset of the already-committed
`shipping_visitExpr_correct'`'s. No axiom of ours. -/
theorem shipping_erase_correct_firstorderι_of_shape
    {safety : DefinitionSafety} {kenv : Lean.Kernel.Environment}
    {env : VEnv} (henv : env.WF) {Us : List Name}
    {known : Name → Prop} {Γ : ErasureCtx} {ia : IotaArities}
    {Esrc : SEnv} {E : GlobalDeclarations}
    (hspec : PatsIotaSpec safety kenv env)
    (hcon : SEnvConsistent env Us Esrc)
    (hshape : IotaShape safety kenv Γ ia Esrc)
    (hdelta : ErasesEnvDeltaData env Us Γ Esrc E)
    (hctorenv : ErasesEnvCtor Γ E)
    (hcasesenv : ErasesEnvCases Γ E)
    (hcoh : CtorFieldsCoherent Γ)
    (hiacoh : IotaArityCoherent Γ ia)
    (hflat : FlatCaseFields Γ)
    (hrel : IotaRelevant env Us Γ)
    (hcc : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
             Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none)
    (hnfenv : NoFixEnv E)
    (hclenv : ClosedEnv E)
    {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
    {e v : Expr} {ve : VExpr} {t : LBTerm}
    {s s' : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    (hrun : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w')
    (hinv : BridgeInv env Us known Γ (gw w) ctx s [])
    (hsup : Supported known Γ e)
    (htr : TrExprS env Us [] e ve)
    (hnb : NoBlock t)
    (hnfx : NoFix t)
    (hcl : LBClosed t 0)
    (hev : SEvalDataι Γ ia Esrc e v)
    (hfo : FirstOrderValue env Us Γ [] v) :
    ∃ t', WcbvEval E appliedFlags t t' ∧
      (∃ vve, TrExprS env Us [] v vve) ∧
      Erases env Us Γ [] v t' ∧ NoBlock t' ∧ LBClosed t' 0 ∧
      ∀ tu, Erases env Us Γ [] v tu → NoBlock tu → tu = t' :=
  shipping_erase_correct_firstorderι henv hcon
    (iotaConsistent_of_shape henv hspec hcon hshape)
    hdelta hctorenv hcasesenv hcoh hiacoh hflat hrel hcc hnfenv hclenv H HD C
    hrun hinv hsup htr hnb hnfx hcl hev hfo

/-- **D3ι with every `Γ`/`E` env-consistency premise sourced from registration.** The ι
analogue of `shipping_erase_correct_firstorder_registered`, and a step further: not only
`hdelta` but the whole `Γ`-population block is replaced by the registration records that
a cold-start DAG walk (P3.13, deferred) would discharge from the actual `visitMutual`
run.

Discharged internally: `ErasesEnvDeltaData` by
`erasesEnvDeltaData_of_registeredClosureData`, `ErasesEnvCtor` by
`erasesEnvCtor_of_registeredCtors`, `ErasesEnvCases` by
`erasesEnvCases_of_registeredCases` (and thence `ErasesEnvCasesι` by
`ErasesEnvCases.nonProp`), and `CtorFieldsCoherent` by
`ctorFieldsCoherent_of_registered`. The ι fragment goes further than the non-ι capstone
here because `CtorFieldsCoherent` has *no* single-record discharge — it needs the
constructor, `casesOn` and field-count records jointly, so leaving one of them as a
direct env premise would buy nothing.

What is **not** registration-derived, by nature: `IotaArityCoherent` (a fact about
`CasesInfo`, i.e. the `casesOn`'s telescope, not about the target env), `FlatCaseFields`
(the scope restriction), `ClosedEnv`/`NoFixEnv` (target-body facts), the disjointness
`hcc`, and the ι interface premise. -/
theorem shipping_erase_correct_firstorderι_registered
    {env : VEnv} (henv : env.WF) {Us : List Name}
    {known : Name → Prop} {Γ : ErasureCtx} {ia : IotaArities}
    {Esrc : SEnv} {E : GlobalDeclarations}
    (hcon : SEnvConsistent env Us Esrc)
    (hiota : IotaConsistent env Us Γ ia)
    (hregdelta : RegisteredClosureData env Us Γ Esrc E)
    (hregctors : RegisteredCtors Γ E)
    (hregcases : RegisteredCases Γ E)
    (hregfields : RegisteredCtorFieldsAll Γ E)
    (hiacoh : IotaArityCoherent Γ ia)
    (hflat : FlatCaseFields Γ)
    (hrel : IotaRelevant env Us Γ)
    (hcc : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
             Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none)
    (hnfenv : NoFixEnv E)
    (hclenv : ClosedEnv E)
    {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
    {e v : Expr} {ve : VExpr} {t : LBTerm}
    {s s' : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    (hrun : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w')
    (hinv : BridgeInv env Us known Γ (gw w) ctx s [])
    (hsup : Supported known Γ e)
    (htr : TrExprS env Us [] e ve)
    (hnb : NoBlock t)
    (hnfx : NoFix t)
    (hcl : LBClosed t 0)
    (hev : SEvalDataι Γ ia Esrc e v)
    (hfo : FirstOrderValue env Us Γ [] v) :
    ∃ t', WcbvEval E appliedFlags t t' ∧
      (∃ vve, TrExprS env Us [] v vve) ∧
      Erases env Us Γ [] v t' ∧ NoBlock t' ∧ LBClosed t' 0 ∧
      ∀ tu, Erases env Us Γ [] v tu → NoBlock tu → tu = t' :=
  shipping_erase_correct_firstorderι henv hcon hiota
    (erasesEnvDeltaData_of_registeredClosureData hregdelta)
    (erasesEnvCtor_of_registeredCtors hregctors)
    (erasesEnvCases_of_registeredCases hregcases)
    (ctorFieldsCoherent_of_registered hregctors hregcases hregfields)
    hiacoh hflat hrel hcc hnfenv hclenv H HD C hrun hinv hsup htr hnb hnfx hcl hev hfo

/-! ## Non-vacuity guards

### What is constructible, and what is not

The end-to-end guard — a concrete run in which the **ι rule itself** contracts a real
pattern match — is **not** constructible at this pin, for exactly the reason recorded at
`iotaConsistent_of_shape` and `IotaRelevant`: it would need `IotaConsistent` (or
`PatsIotaSpec` + `IotaShape`) instantiated, hence `env.WF` for a `pats`-carrying `VEnv`,
and `VEnv.WF` is unconstructible for one upstream (`VEnv.Ordered` has no `addPat`
clause; `addInduct_WF` and `addDecl.WF`'s `inductDecl` case are `sorry`). `IotaShape`
additionally requires a concrete `Lean.Kernel.Environment` carrying the recursor. The halves
are guarded where they live: `envι_iota_fires` (the ι machinery fires and yields a real
`IsDefEqU`) and the four `betaN_*_guard`s (`IotaShape`'s `Expr` equations), all in
`IotaDischarge.lean`.

What **is** constructible, and is built here, is the whole `Γ`/`E` **certificate block**
at a single genuinely registered inductive — which no existing guard does: the ι
coherence guards live at `gΓι` (`EnvErasureNonrec.lean`, a *field-carrying* `AC`, hence
not flat) and the flatness guards at `gΓflat` (`ErasesCorrectIota.lean`, whose `Γ` is not
backed by registration records). `ΓFOι`/`EFOd` below is both: registered *and* flat, so
every certificate premise of D3ι holds at one and the same `(Γ, ia, E)`, and D3ι *fires*
there, on the nullary first-order constructor `c`.

Left hypothetical, matching the D3 guard's own discipline: the run `hrun`/`hinv`/`hsup`
and the three runtime bundles `H`/`HD`/`C` (opaque primitives), plus the two ι trust
items `IotaConsistent` and `IotaRelevant`. -/

/-- The guard's `Γ`: `ΓFOd` (the nullary constructor `c` of `I`, `FirstOrder.lean`)
**plus** a registered `casesOn` head `con` eliminating the same `I` — zero parameters,
one (nullary) constructor, discriminant at position `np + nmot + nidx = 0 + 1 + 0`. -/
def ΓFOι : ErasureCtx where
  inductives := fun _ => none
  constants := toKername
  ctors := fun n => if n = `c then some (⟨toKername `I, 0⟩, 0) else none
  ctorArities := fun n => if n = `c then some 0 else none
  casesOns := fun n => if n = `con then some (⟨toKername `I, 0⟩, 0) else none
  ctorFields := fun _ => some [0]
  casesDiscrPos := fun n => if n = `con then some 1 else none

/-- The matching `IotaArities` for `con`: `numMotives = 1`, `numIndices = 0`,
`numMinors = 1`. -/
def iaFOι : IotaArities := fun n => if n = `con then some (1, 0, 1) else none

theorem ΓFOι_ctorsC : ΓFOι.ctors `c = some (⟨toKername `I, 0⟩, 0) := by unfold ΓFOι; simp
theorem ΓFOι_ctorAritiesC : ΓFOι.ctorArities `c = some 0 := by unfold ΓFOι; simp
theorem ΓFOι_casesC : ΓFOι.casesOns `c = none := by unfold ΓFOι; simp

/-- The constructor/`casesOn` disjointness premise `hcc`, at the guard's `Γ`. -/
theorem ΓFOι_cc {cn : Name} {iid : InductiveId} {cidx : Nat} :
    ΓFOι.ctors cn = some (iid, cidx) → ΓFOι.casesOns cn = none := by
  intro hc
  by_cases h : cn = `c
  · subst h; exact ΓFOι_casesC
  · simp [ΓFOι, if_neg h] at hc

/-- `c` is backed by `EFOd`'s `register_inductive` record: `npars + nargs = 0 + 0`. -/
theorem ΓFOι_registeredCtors : RegisteredCtors ΓFOι EFOd := by
  intro cn iid cidx hc
  by_cases h : cn = `c
  · subst h
    simp only [ΓFOι] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨mibFOd, oibFOd, { name := "c", nargs := 0 }, rfl, rfl, rfl, ΓFOι_ctorAritiesC⟩
  · simp [ΓFOι, if_neg h] at hc

/-- `con` is backed by the same record: `npars = 0 = numParams`, and `I` is registered
**non-propositional**, which is what the target ι rule's guard needs. -/
theorem ΓFOι_registeredCases : RegisteredCases ΓFOι EFOd := by
  intro con iid numParams hcon
  by_cases h : con = `con
  · subst h
    simp only [ΓFOι] at hcon
    obtain ⟨rfl, rfl⟩ := hcon
    exact ⟨mibFOd, oibFOd, rfl, rfl, rfl, rfl⟩
  · simp [ΓFOι, if_neg h] at hcon

/-- The field-count list `[0]` is exactly `EFOd`'s `nargs` column. -/
theorem ΓFOι_registeredCtorFields : RegisteredCtorFieldsAll ΓFOι EFOd := by
  intro con iid np hcon
  by_cases h : con = `con
  · subst h
    simp only [ΓFOι] at hcon
    obtain ⟨rfl, rfl⟩ := hcon
    exact ⟨mibFOd, oibFOd, rfl, rfl, rfl⟩
  · simp [ΓFOι, if_neg h] at hcon

/-- Derived: `ErasesEnvCtor`. -/
theorem ΓFOι_erasesEnvCtor : ErasesEnvCtor ΓFOι EFOd :=
  erasesEnvCtor_of_registeredCtors ΓFOι_registeredCtors

/-- Derived: `ErasesEnvCases` — and hence `ErasesEnvCasesι` by `.nonProp`. -/
theorem ΓFOι_erasesEnvCases : ErasesEnvCases ΓFOι EFOd :=
  erasesEnvCases_of_registeredCases ΓFOι_registeredCases

/-- Derived: the target-side ι precondition fires at the registered head. -/
theorem ΓFOι_erasesEnvCasesι : ErasesEnvCasesι ΓFOι EFOd :=
  fun hc => ΓFOι_erasesEnvCases.nonProp hc

/-- Derived: `CtorFieldsCoherent` — `ctorArities c = 0` decomposes as `npars 0 + nfs[0] 0`. -/
theorem ΓFOι_ctorFieldsCoherent : CtorFieldsCoherent ΓFOι :=
  ctorFieldsCoherent_of_registered ΓFOι_registeredCtors ΓFOι_registeredCases
    ΓFOι_registeredCtorFields

/-- `IotaArityCoherent`: `discrPos = 1 = np + nmot + nidx`, constructor count `1 = nmin`. -/
theorem ΓFOι_iotaArityCoherent : IotaArityCoherent ΓFOι iaFOι := by
  intro con iid np nmot nidx nmin hcases hia
  by_cases h : con = `con
  · subst h
    simp only [ΓFOι, iaFOι] at hcases hia
    obtain ⟨rfl, rfl⟩ := hcases
    obtain ⟨rfl, rfl, rfl⟩ := hia
    exact ⟨by simp [ΓFOι], [0], rfl, rfl⟩
  · simp [ΓFOι, if_neg h] at hcases

/-- `FlatCaseFields`: the eliminated inductive's only constructor retains no fields. -/
theorem ΓFOι_flat : FlatCaseFields ΓFOι := by
  intro con iid np nfs hcases hnfs j hj
  simp only [ΓFOι] at hnfs
  obtain rfl : nfs = [0] := (Option.some.inj hnfs).symm
  match j, hj with
  | 0, _ => rfl

/-- `ClosedEnv EFOd` — the guard env declares an inductive and no constant body. -/
theorem EFOd_closedEnv : ClosedEnv EFOd := by
  intro kn body h
  simp only [EFOd, LBTerm.envLookup] at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h

/-- `NoFixEnv EFOd` — same reason. -/
theorem EFOd_noFixEnv : NoFixEnv EFOd := by
  intro kn body' h
  simp only [EFOd, LBTerm.envLookup] at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h

/-- `c`'s value is first-order at the ι guard's `Γ` (modulo the one lean4lean-blocked
arity side condition, exactly as `envFO_foC_d`). -/
theorem envFO_foC_ι (harity : ¬ IsArityUpTo envFO 0 [] (.const `I [])) :
    FirstOrderValue envFO [] ΓFOι [] (.const `c []) := by
  have heq : (.const `c [] : Expr) = ([] : List Expr).foldl Expr.app (.const `c []) := rfl
  rw [heq]
  exact .ctor `c [] ⟨toKername `I, 0⟩ 0 ΓFOι_ctorsC ΓFOι_casesC
    (by simpa using envFO_informativeC harity) (fun i h => absurd h (by simp))

/-- **The certificate block is jointly satisfiable at one registered, flat inductive.**
Every `Γ`/`E`-level premise of D3ι, at `(ΓFOι, iaFOι, EFOd)` — all of them *derived* from
the registration records where a discharge exists. This is the guard the ι capstone can
actually carry; see the section docstring for the one that it cannot. -/
theorem ΓFOι_certificates :
    ErasesEnvCtor ΓFOι EFOd ∧ ErasesEnvCases ΓFOι EFOd ∧ ErasesEnvCasesι ΓFOι EFOd ∧
      CtorFieldsCoherent ΓFOι ∧ IotaArityCoherent ΓFOι iaFOι ∧ FlatCaseFields ΓFOι ∧
      NoFixEnv EFOd ∧ ClosedEnv EFOd ∧
      (∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
        ΓFOι.ctors cn = some (iid, cidx) → ΓFOι.casesOns cn = none) :=
  ⟨ΓFOι_erasesEnvCtor, ΓFOι_erasesEnvCases, ΓFOι_erasesEnvCasesι, ΓFOι_ctorFieldsCoherent,
    ΓFOι_iotaArityCoherent, ΓFOι_flat, EFOd_noFixEnv, EFOd_closedEnv, ΓFOι_cc⟩

/-- **D3ι fires.** On the nullary first-order constructor `c` at the registered flat
inductive above: the source-env hypotheses hold vacuously (empty `Esrc`), the whole
certificate block is `ΓFOι_certificates`, the source `c` `SEvalDataι`-evaluates to
itself, and the theorem produces `t'` together with its uniqueness. Hypothetical: the run
(`hrun`/`hinv`/`hsup`), the three runtime bundles, the target-side structural facts about
the run's output `t` (`NoBlock`/`NoFix`/`LBClosed`), and the two ι trust items
(`IotaConsistent`, `IotaRelevant`). -/
example (harity : ¬ IsArityUpTo envFO 0 [] (.const `I []))
    (hiota : IotaConsistent envFO [] ΓFOι iaFOι)
    (hrel : IotaRelevant envFO [] ΓFOι)
    (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps envFO [] ΓFOι gw) (HD : DataBridgeHyps ΓFOι gw)
    (C : CasesBridgeHyps ΓFOι gw)
    (s s' : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld) (t : LBTerm)
    (hrun : Erasure.visitExpr (.const `c []) s ctx cctx ref w = .ok (t, s') w')
    (hinv : BridgeInv envFO [] (fun _ => True) ΓFOι (gw w) ctx s [])
    (hsup : Supported (fun _ => True) ΓFOι (.const `c []))
    (hnb : NoBlock t) (hnfx : NoFix t) (hcl : LBClosed t 0) :
    ∃ t', WcbvEval EFOd appliedFlags t t' ∧
      (∃ vve, TrExprS envFO [] [] (.const `c []) vve) ∧
      Erases envFO [] ΓFOι [] (.const `c []) t' ∧ NoBlock t' ∧ LBClosed t' 0 ∧
      ∀ tu, Erases envFO [] ΓFOι [] (.const `c []) tu → NoBlock tu → tu = t' := by
  have heq : (.const `c [] : Expr) = ([] : List Expr).foldl Expr.app (.const `c []) := rfl
  refine shipping_erase_correct_firstorderι envFO_wf (Us := []) (Esrc := fun _ => none)
    (E := EFOd) (ia := iaFOι) ?_ hiota ?_ ΓFOι_erasesEnvCtor ΓFOι_erasesEnvCases
    ΓFOι_ctorFieldsCoherent ΓFOι_iotaArityCoherent ΓFOι_flat hrel ΓFOι_cc
    EFOd_noFixEnv EFOd_closedEnv H HD C hrun hinv hsup envFO_trC hnb hnfx hcl ?_
    (envFO_foC_ι harity)
  · intro Δ n us body cve h; exact absurd h (by simp)   -- SEnvConsistent, vacuous
  · intro Δ n body h; exact absurd h (by simp)          -- ErasesEnvDeltaData, vacuous
  · rw [heq]                                            -- SEvalDataι: c ⇓ c
    exact .ctor_val ΓFOι_ctorsC ΓFOι_ctorAritiesC (by simp) rfl (fun i h => absurd h (by simp))

end LeanToLambdaBox
