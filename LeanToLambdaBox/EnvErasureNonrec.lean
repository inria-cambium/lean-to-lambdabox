import LeanToLambdaBox.VisitExprRefines
import LeanToLambdaBox.DataBridgeHyps
import LeanToLambdaBox.ErasesCorrectData
import LeanToLambdaBox.Semantics.Metatheory
import LeanToLambdaBox.PrepareHyps

/-!
# Cold-start env-consistency discharge: the non-recursive + inductive fragment (P3-v1)

This file discharges — as **theorems about the constructed global declarations**, no
longer as bare premises — the environment-consistency hypotheses that the forward
simulations (`erases_correct`, `erases_correct_data`) assume, for the fragment with **no
value recursion**:

* `ErasesEnvCtor` (`ErasesCorrectData.lean:529`) and the `casesOn`-analogue
  `ErasesEnvCases` (defined here), from `register_inductive`'s local arity computation;
* `ErasesEnvDelta` (`ErasesCorrect.lean:247`) / `ErasesEnvDeltaData`
  (`ErasesCorrectData.lean:537`) for **non-recursive** constants, via the shipping
  `visitExpr → Erases` bridge (`visitExpr_refines_erases`).

It composes **no** final cold-start theorem (that is P3-v2b) and touches **no**
forward-simulation theorem, no `Erases` constructor, and no `.fix` reasoning. The
cold-start DAG registration (which constants/inductives actually land in `E`, and that
each entry is consistent) is isolated behind clean `Prop` hypotheses
(`RegisteredCtors`, `RegisteredCases`, `RegisteredClosure`, `RegisteredClosureData`) —
the analogues of `PrepareHyps`/`BridgeHyps`, and what P3-v2b will discharge. These are
`Prop` hypotheses, **never axioms**.

## The `register_inductive` arity computation (feeds `ErasesEnvCtor`/`ErasesEnvCases`)

`register_inductive` (`Erasure.lean:192`) conses **one** `(mutualBlockName,
.inductiveDecl mutual_body)` entry onto `gdecls`, where `mutual_body.npars =
indinfo.numParams` (`:241`) and each constructor stores `nargs := Array.count .keep
argmask` (`:222`) in its `ConstructorBody` (`:223`). The target-side lookup
`Semantics/Env.constructorArity` (`:44`) reads back exactly `body.npars + cb.nargs`,
which is MetaRocq's `cstr_arity = ind_npars + cstr_nargs`. So agreement between the
abstract `Γ.ctorArities` and the concrete `constructorArity E` is a *local, fix-free*
arithmetic identity, once the registration record links the two — which is precisely
`RegisteredCtors`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

/-! ## Part 1 — `ErasesEnvCtor` / `ErasesEnvCases` from the inductive registration -/

/-- **Per-constructor registration record.** What `register_inductive` puts in `E` and
what the bridge records in `Γ` for a constructor `cn` at `(iid, cidx)`: the single
`.inductiveDecl body` entry, its `oib`, the constructor's `ConstructorBody cb`, and
`Γ.ctorArities cn = some (body.npars + cb.nargs)` — the *same* `npars + nargs`
`register_inductive` computed locally. -/
def RegisteredCtor (Γ : ErasureCtx) (E : GlobalDeclarations) (cn : Name)
    (iid : InductiveId) (cidx : Nat) : Prop :=
  ∃ (body : MutualInductiveBody) (oib : OneInductiveBody) (cb : ConstructorBody),
    LBTerm.envLookup E iid.mutualBlockName = some (.inductiveDecl body) ∧
    body.bodies[iid.idx]? = some oib ∧
    oib.ctors[cidx]? = some cb ∧
    Γ.ctorArities cn = some (body.npars + cb.nargs)

/-- **Closure-level constructor registration** (a clean `Prop` hypothesis; P3-v2b's DAG
registration discharges it): every constructor `Γ` knows is backed by a matching
`register_inductive` record in `E`. -/
def RegisteredCtors (Γ : ErasureCtx) (E : GlobalDeclarations) : Prop :=
  ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
    Γ.ctors cn = some (iid, cidx) → RegisteredCtor Γ E cn iid cidx

/-- **Target-side `casesOn` env consistency** — the `casesOn` analogue of
`ErasesEnvCtor`. For every registered `casesOn` head `con` (`Γ.casesOns con = some (iid,
numParams)`), the target env `E` has the inductive `iid` registered as an
`.inductiveDecl` whose parameter count matches `numParams` (so the `.case (iid,
numParams)` node the `Erases.cases` rule emits agrees with `E`, and the target `iota`
rule's `isPropositionalInductive`/`iota_red` lookups are well-defined) and which is
**not propositional** — the ι rule `WcbvEval.iota` fires only on a non-propositional
inductive (a propositional one reduces by `iota_sing`, which needs `with_prop_case`).
The last conjunct is exposed as `ErasesEnvCases.nonProp`. -/
def ErasesEnvCases (Γ : ErasureCtx) (E : GlobalDeclarations) : Prop :=
  ∀ {con : Name} {iid : InductiveId} {numParams : Nat},
    Γ.casesOns con = some (iid, numParams) →
    ∃ (body : MutualInductiveBody) (oib : OneInductiveBody),
      LBTerm.envLookup E iid.mutualBlockName = some (.inductiveDecl body) ∧
      body.bodies[iid.idx]? = some oib ∧
      body.npars = numParams ∧
      oib.propositional = false

/-- **Closure-level `casesOn` registration** (a clean `Prop` hypothesis; P3-v2b
discharges it). Same shape as `ErasesEnvCases`, tagged as the *registration* record so
the discharge theorem reads as "registration ⟹ env consistency". -/
def RegisteredCases (Γ : ErasureCtx) (E : GlobalDeclarations) : Prop :=
  ∀ {con : Name} {iid : InductiveId} {numParams : Nat},
    Γ.casesOns con = some (iid, numParams) →
    ∃ (body : MutualInductiveBody) (oib : OneInductiveBody),
      LBTerm.envLookup E iid.mutualBlockName = some (.inductiveDecl body) ∧
      body.bodies[iid.idx]? = some oib ∧
      body.npars = numParams ∧
      oib.propositional = false

/-- **Per-inductive field-count registration record.** `Γ.ctorFields` is exactly the
`nargs` column of the `.inductiveDecl` entry `register_inductive` conses onto `gdecls`
(`Erasure.lean`: `nargs := Array.count .keep argmask`) — the *retained* field counts. -/
def RegisteredCtorFields (Γ : ErasureCtx) (E : GlobalDeclarations) (iid : InductiveId) :
    Prop :=
  ∃ (body : MutualInductiveBody) (oib : OneInductiveBody),
    LBTerm.envLookup E iid.mutualBlockName = some (.inductiveDecl body) ∧
    body.bodies[iid.idx]? = some oib ∧
    Γ.ctorFields iid = some (oib.ctors.map (·.nargs))

/-- Closure-level version (a clean `Prop`; P3-v2b's DAG registration discharges it):
every inductive some registered `casesOn` eliminates has its field-count list recorded. -/
def RegisteredCtorFieldsAll (Γ : ErasureCtx) (E : GlobalDeclarations) : Prop :=
  ∀ {con : Name} {iid : InductiveId} {np : Nat},
    Γ.casesOns con = some (iid, np) → RegisteredCtorFields Γ E iid

/-- **`ErasesEnvCtor` discharge.** The abstract `Γ.ctorArities` agrees with the concrete
`constructorArity E` because both are `register_inductive`'s `body.npars + cb.nargs`
(the local `npars + count .keep argmask`). Fix-free, self-contained. -/
theorem erasesEnvCtor_of_registeredCtors {Γ : ErasureCtx} {E : GlobalDeclarations}
    (h : RegisteredCtors Γ E) : ErasesEnvCtor Γ E := by
  intro cn iid cidx ar hc har
  obtain ⟨body, oib, cb, henv, hbod, hctor, harity⟩ := h hc
  have hare : body.npars + cb.nargs = ar :=
    Option.some.inj (harity.symm.trans har)
  simp only [constructorArity, henv, hbod, hctor, Option.map_some, hare]

/-- **`ErasesEnvCases` discharge.** Immediate from the registration record: the same
`.inductiveDecl` entry, `npars = numParams` and non-propositionality. -/
theorem erasesEnvCases_of_registeredCases {Γ : ErasureCtx} {E : GlobalDeclarations}
    (h : RegisteredCases Γ E) : ErasesEnvCases Γ E :=
  fun hcon => h hcon

/-- **The target-side ι precondition, read off `ErasesEnvCases`.** `WcbvEval.iota`'s
`isPropositionalInductive E iid = false` premise, by unfolding the lookup chain against
the registration record. -/
theorem ErasesEnvCases.nonProp {Γ : ErasureCtx} {E : GlobalDeclarations}
    (h : ErasesEnvCases Γ E) {con : Name} {iid : InductiveId} {np : Nat}
    (hc : Γ.casesOns con = some (iid, np)) : isPropositionalInductive E iid = false := by
  obtain ⟨body, oib, henv, hbod, _, hprop⟩ := h hc
  simp only [isPropositionalInductive, henv, hbod, hprop]

/-- **`CtorFieldsCoherent` discharge.** The same arithmetic `erasesEnvCtor_of_registeredCtors`
does: `RegisteredCtor` gives `Γ.ctorArities cn = some (body.npars + cb.nargs)`,
`RegisteredCases` gives `body.npars = np`, and `RegisteredCtorFields` gives
`nfs = oib.ctors.map (·.nargs)`, hence `nfs[cidx] = cb.nargs` from `oib.ctors[cidx]? = some
cb`. The three `envLookup`/`bodies[…]?` witnesses are pinned to the same `body`/`oib` by
`Option.some.inj`. -/
theorem ctorFieldsCoherent_of_registered {Γ : ErasureCtx} {E : GlobalDeclarations}
    (hc : RegisteredCtors Γ E) (hcs : RegisteredCases Γ E)
    (hcf : RegisteredCtorFieldsAll Γ E) : CtorFieldsCoherent Γ := by
  intro con cn iid np cidx nfs hcases hnfs hctors
  obtain ⟨body, oib, cb, henv, hbod, hcb, harity⟩ := hc hctors
  obtain ⟨body2, oib2, henv2, hbod2, hnpars, _⟩ := hcs hcases
  obtain ⟨body3, oib3, henv3, hbod3, hfields⟩ := hcf hcases
  have hb2 : body2 = body := by
    have h := Option.some.inj (henv2.symm.trans henv); injection h
  have hb3 : body3 = body := by
    have h := Option.some.inj (henv3.symm.trans henv); injection h
  rw [hb2] at hbod2 hnpars
  rw [hb3] at hbod3
  have ho3 : oib3 = oib := Option.some.inj (hbod3.symm.trans hbod)
  rw [ho3] at hfields
  obtain rfl : nfs = oib.ctors.map (·.nargs) := Option.some.inj (hnfs.symm.trans hfields)
  have hlt0 : cidx < oib.ctors.length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hcb
    exact absurd hcb (by simp)
  have hlt : cidx < (oib.ctors.map (·.nargs)).length := by rw [List.length_map]; exact hlt0
  refine ⟨hlt, ?_⟩
  have hcbn : (oib.ctors.map (·.nargs))[cidx]'hlt = cb.nargs := by
    rw [List.getElem_map]
    have h := List.getElem?_eq_getElem hlt0
    rw [hcb] at h
    rw [(Option.some.inj h).symm]
  rw [harity, hcbn, hnpars]

/-! ### Non-vacuity guards for Part 1

We reuse the concrete one-parameter, one-field inductive `AC`/`mk`
(`Semantics/Metatheory.lean`: `acKn`/`acIid`/`acOIB`/`acΓ`, with `ac_arity :
constructorArity acΓ acIid 0 = some 2`) — a genuinely *registered* constructor, so the
guards are non-vacuous (the `ctors`/`casesOns` maps are not the all-`none` function). -/

/-- A concrete `Γ` registering `AC.mk` as constructor `(acIid, 0)` with arity `2`. -/
private def gΓctor : ErasureCtx where
  inductives := fun _ => none
  constants := fun _ => default
  ctors := fun _ => some (acIid, 0)
  ctorArities := fun _ => some 2
  casesOns := fun _ => none

/-- A concrete `Γ` registering an `AC.casesOn` head as `(acIid, 1)` (npars = 1). -/
private def gΓcases : ErasureCtx where
  inductives := fun _ => none
  constants := fun _ => default
  ctors := fun _ => none
  ctorArities := fun _ => none
  casesOns := fun _ => some (acIid, 1)

/-- Non-vacuity: `RegisteredCtors` holds at the concrete `(gΓctor, acΓ)` — `AC.mk`'s
`register_inductive` record `body.npars + cb.nargs = 1 + 1 = 2` matches. -/
theorem gΓctor_registeredCtors : RegisteredCtors gΓctor acΓ := by
  intro cn iid cidx hc
  simp only [gΓctor, Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact ⟨_, acOIB, { name := "mk", nargs := 1 }, rfl, rfl, rfl, rfl⟩

/-- Non-vacuity: `ErasesEnvCtor gΓctor acΓ` is then *derived*, and genuinely fires —
`constructorArity acΓ acIid 0 = some 2` matches `gΓctor.ctorArities`. -/
theorem gΓctor_erasesEnvCtor : ErasesEnvCtor gΓctor acΓ :=
  erasesEnvCtor_of_registeredCtors gΓctor_registeredCtors

/-- Non-vacuity: `RegisteredCases` holds at `(gΓcases, acΓ)` — the inductive is
registered with `npars = 1`. -/
theorem gΓcases_registeredCases : RegisteredCases gΓcases acΓ := by
  intro con iid numParams hcon
  simp only [gΓcases, Option.some.injEq, Prod.mk.injEq] at hcon
  obtain ⟨rfl, rfl⟩ := hcon
  exact ⟨_, acOIB, rfl, rfl, rfl, rfl⟩

/-- Non-vacuity: `ErasesEnvCases gΓcases acΓ` is derived. -/
theorem gΓcases_erasesEnvCases : ErasesEnvCases gΓcases acΓ :=
  erasesEnvCases_of_registeredCases gΓcases_registeredCases

/-! ### Non-vacuity for the ι coherence predicates (ι Task 3)

`CtorFieldsCoherent`/`IotaArityCoherent` relate the constructor side and the `casesOn`
side of `Γ`, so their guard needs a `Γ` registering **both** — `gΓcases` registers only a
`casesOn` and `gΓctor` only a constructor. `gΓι` registers both against the same `AC`
(one parameter, one field, so `ctorArities = 1 + 1` decomposes non-degenerately), with a
`casesOn` head `con` at `discrPos = np + nmot + nidx = 1 + 1 + 0 = 2`. -/

/-- A concrete `Γ` registering `AC.mk` as `(acIid, 0)` **and** an `AC.casesOn` head
`con` at `(acIid, 1)`, with the field-count list and the discriminant position that
`register_inductive` + `CasesInfo` would record. -/
private def gΓι : ErasureCtx where
  inductives := fun _ => none
  constants := fun _ => default
  ctors := fun n => if n = `mk then some (acIid, 0) else none
  ctorArities := fun n => if n = `mk then some 2 else none
  casesOns := fun n => if n = `con then some (acIid, 1) else none
  ctorFields := fun _ => some [1]
  casesDiscrPos := fun n => if n = `con then some 2 else none

/-- The matching `IotaArities`: `numMotives = 1`, `numIndices = 0`, `numMinors = 1`. -/
private def gIAι : IotaArities := fun n => if n = `con then some (1, 0, 1) else none

theorem gΓι_registeredCtors : RegisteredCtors gΓι acΓ := by
  intro cn iid cidx hc
  by_cases h : cn = `mk
  · subst h
    simp [gΓι] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨_, acOIB, { name := "mk", nargs := 1 }, rfl, rfl, rfl, by simp [gΓι]⟩
  · simp [gΓι, if_neg h] at hc

theorem gΓι_registeredCases : RegisteredCases gΓι acΓ := by
  intro con iid numParams hcon
  by_cases h : con = `con
  · subst h
    simp [gΓι] at hcon
    obtain ⟨rfl, rfl⟩ := hcon
    exact ⟨_, acOIB, rfl, rfl, rfl, rfl⟩
  · simp [gΓι, if_neg h] at hcon

theorem gΓι_registeredCtorFields : RegisteredCtorFieldsAll gΓι acΓ := by
  intro con iid np hcon
  by_cases h : con = `con
  · subst h
    simp [gΓι] at hcon
    obtain ⟨rfl, rfl⟩ := hcon
    exact ⟨_, acOIB, rfl, rfl, rfl⟩
  · simp [gΓι, if_neg h] at hcon

/-- Non-vacuity: `CtorFieldsCoherent gΓι` is *derived* from the three registration
records, and genuinely fires — `ctorArities mk = 2` decomposes as `npars 1 + nfs[0] 1`. -/
theorem gΓι_ctorFieldsCoherent : CtorFieldsCoherent gΓι :=
  ctorFieldsCoherent_of_registered gΓι_registeredCtors gΓι_registeredCases
    gΓι_registeredCtorFields

/-- Non-vacuity: `IotaArityCoherent gΓι gIAι` — `discrPos = 2 = np + nmot + nidx` with
`np = 1`, and the constructor count `|[1]| = 1 = numMinors`. -/
theorem gΓι_iotaArityCoherent : IotaArityCoherent gΓι gIAι := by
  intro con iid np nmot nidx nmin hcases hia
  by_cases h : con = `con
  · subst h
    simp [gΓι, gIAι] at hcases hia
    obtain ⟨rfl, rfl⟩ := hcases
    obtain ⟨rfl, rfl, rfl⟩ := hia
    exact ⟨rfl, [1], rfl, rfl⟩
  · simp [gΓι, if_neg h] at hcases

/-- Non-vacuity: the derived `ErasesEnvCases.nonProp` fires — `AC` is registered
non-propositional, so the target ι rule's guard is satisfied. -/
theorem gΓι_nonProp : isPropositionalInductive acΓ acIid = false :=
  ErasesEnvCases.nonProp (erasesEnvCases_of_registeredCases gΓι_registeredCases)
    (con := `con) (np := 1) (by simp [gΓι])

/-! ## Part 2 — non-recursive `ErasesEnvDelta` via the `visitExpr → Erases` bridge

`visitMutual`'s non-recursive branch (`Erasure.lean:886`) erases a constant `n` by
`t := visitExpr (prepare_erasure (ci.value! n))` under `fixvars := none` (`:889`) — so
the body is **plain**, never a `.fix` — and conses `(toKername n, .constantDecl ⟨some
t⟩)` (`:892`). The bridge `visitExpr_refines_erases` turns that run into an `Erases`
fact. `erases_nonrec_const_body` is exactly that invocation, specialized to the
cold-start context `Δ = []` (constant bodies are closed). -/

/-- **Bridge invocation for one non-recursive constant body.** A successful cold-start
`visitExpr prepbody` run (where `prepbody = prepare_erasure (ci.value! n)`) erases
`prepbody` to `body'` — the `t` stored at `Erasure.lean:892`. This is a `Δ = []`
specialization of `visitExpr_refines_erases`; its premises' non-vacuity is inherited
from `visitExpr_refines_erases`'s own guards (`VisitExprRefines.lean` NonVacuity), plus
the `Δ = []` invariant guard below. -/
theorem erases_nonrec_const_body {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
    (henv : env.Ordered)
    {prepbody : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {body' : LBTerm}
    {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : Erasure.visitExpr prepbody s ctx cctx ref w = .ok (body', s') w')
    (hinv : BridgeInv env Us known Γ (gw w) ctx s [])
    (hsupp : Supported known Γ prepbody)
    (hex : ∃ ve, TrExprS env Us [] prepbody ve) :
    Erases env Us Γ [] prepbody body' :=
  (visitExpr_refines_erases H HD C henv _ _ _ _ _ _ _ _ _ hrun _ hinv hsupp hex).1

/-- **Cold-start closure registration for the non-recursive fragment** (a clean `Prop`
hypothesis; P3-v2b's DAG registration discharges it). For every source constant `n`
with an unfolding `Esrc n = some body`:

* `disj` — `n` is a genuine constant, not a registered constructor/`casesOn` head;
* `erase` — the run consed `(Γ.constants n, .constantDecl ⟨some body'⟩)` onto `E`, and
  `body` erases to that **plain** `body'` in *any* context `Δ`.

The `∀ {Δ}` on the `Erases` witness is the constant-body **context-uniformity** the DAG
proof supplies: `body`/`body'` are closed (constant bodies), so `erases_nonrec_const_body`
produces the `Δ = []` instance and closedness lifts it to any `Δ` (the one obligation
folded in here for v2b — provable from closedness + lean4lean weakening, no axiom).

In the cold-start composition `Esrc n` is taken as the *prepared* body
(`prepare_erasure (ci.value! n)`), so `erase`'s `body` matches `erases_nonrec_const_body`'s
`prepbody` verbatim; `PrepareHyps` (`PrepareHyps.lean`) separately ties the prepared
body's source evaluation back to the original. -/
structure RegisteredClosure (env : VEnv) (Us : List Name) (Γ : ErasureCtx)
    (Esrc : SEnv) (E : GlobalDeclarations) : Prop where
  disj : ∀ {n : Name} {body : Expr}, Esrc n = some body →
    Γ.ctors n = none ∧ Γ.casesOns n = none
  erase : ∀ {n : Name} {body : Expr}, Esrc n = some body →
    ∃ body', LBTerm.envLookup E (Γ.constants n) = some (.constantDecl ⟨some body'⟩) ∧
      ∀ {Δ : VLCtx}, Erases env Us Γ Δ body body'

/-- **Non-recursive `ErasesEnvDelta` discharge.** Assembles the per-constant records of
`RegisteredClosure` into the `ErasesEnvDelta` the forward simulation assumes. -/
theorem erasesEnvDelta_of_registeredClosure {env : VEnv} {Us : List Name}
    {Γ : ErasureCtx} {Esrc : SEnv} {E : GlobalDeclarations}
    (h : RegisteredClosure env Us Γ Esrc E) : ErasesEnvDelta env Us Γ Esrc E := by
  intro Δ n body hunf
  obtain ⟨body', hlook, her⟩ := h.erase hunf
  exact ⟨(h.disj hunf).1, (h.disj hunf).2, body', hlook, her⟩

/-- **Data-fragment cold-start closure registration.** As `RegisteredClosure`, plus the
erased body is in **applied (`NoBlock`) form** — what the data forward simulation
`erases_correct_data` needs (via `ErasesEnvDeltaData`). -/
structure RegisteredClosureData (env : VEnv) (Us : List Name) (Γ : ErasureCtx)
    (Esrc : SEnv) (E : GlobalDeclarations) : Prop where
  disj : ∀ {n : Name} {body : Expr}, Esrc n = some body →
    Γ.ctors n = none ∧ Γ.casesOns n = none
  erase : ∀ {n : Name} {body : Expr}, Esrc n = some body →
    ∃ body', LBTerm.envLookup E (Γ.constants n) = some (.constantDecl ⟨some body'⟩) ∧
      (∀ {Δ : VLCtx}, Erases env Us Γ Δ body body') ∧ NoBlock body'

/-- **Non-recursive `ErasesEnvDeltaData` discharge** (data fragment). -/
theorem erasesEnvDeltaData_of_registeredClosureData {env : VEnv} {Us : List Name}
    {Γ : ErasureCtx} {Esrc : SEnv} {E : GlobalDeclarations}
    (h : RegisteredClosureData env Us Γ Esrc E) : ErasesEnvDeltaData env Us Γ Esrc E := by
  intro Δ n body hunf
  obtain ⟨body', hlook, her, hnb⟩ := h.erase hunf
  exact ⟨(h.disj hunf).1, (h.disj hunf).2, body', hlook, her, hnb⟩

/-! ### Non-vacuity guards for Part 2 -/

/-- A source env where a constant unfolds to the closed body `.bvar 0`
(`Erases.bvar` gives a genuine, `Δ`-uniform erasure with no typing premise, so the
witness is fully constructed). -/
private def gEsrcD : SEnv := fun _ => some (.bvar 0)

/-- A concrete `Γ` mapping every constant to a fixed kername, with empty
ctors/casesOns. -/
private def gΓD : ErasureCtx where
  inductives := fun _ => none
  constants := fun _ => rootKername "c"
  ctors := fun _ => none
  ctorArities := fun _ => none
  casesOns := fun _ => none

/-- A concrete `E` binding that kername to the plain body `.bvar 0`. -/
private def gED : GlobalDeclarations := [(rootKername "c", .constantDecl ⟨some (.bvar 0)⟩)]

/-- Non-vacuity: `RegisteredClosure` is realizable at `(gΓD, gEsrcD, gED)` with a genuine
(non-`none`) `Esrc` and a genuine `Erases` witness. -/
theorem gRegisteredClosure (env : VEnv) (Us : List Name) :
    RegisteredClosure env Us gΓD gEsrcD gED where
  disj := fun _ => ⟨rfl, rfl⟩
  erase := by
    intro n body h
    simp only [gEsrcD, Option.some.injEq] at h
    subst h
    exact ⟨.bvar 0, rfl, fun {_} => .bvar 0⟩

/-- Non-vacuity: `ErasesEnvDelta` is then *derived* over the constructed run. -/
theorem gErasesEnvDelta (env : VEnv) (Us : List Name) :
    ErasesEnvDelta env Us gΓD gEsrcD gED :=
  erasesEnvDelta_of_registeredClosure (gRegisteredClosure env Us)

/-- Non-vacuity: the `Δ = []` `BridgeInv` premise of `erases_nonrec_const_body` is
itself realizable (the cold-start empty-context instance), so the bridge invocation's
premise set is not vacuously unsatisfiable. Mirrors `VisitExprRefines.lean` guard (i) at
`Δ = []`.

`hkn` is the invariant's `knames` field (cold-start S2): `Γ` files every constant under
its canonical kername. It is a side condition on `Γ` alone, satisfied by every concrete
`Γ` in the development (`ΓFOd`/`ΓFOι` define `constants := toKername`), so it is passed
in rather than baked into a particular `Γ` here. `hnfv` is the same kind of side
condition for the (W3.1) fixvar agreement: at a top-level entry point neither the run nor
`Γ` installs a block-local fixvar map, so the agreement is `False ↔ False`. -/
theorem gBridgeInv_nil (env : VEnv) (Us : List Name) (Γ : ErasureCtx)
    (hkn : ∀ n : Name, Γ.constants n = toKername n)
    (hnfv : Γ.fixvars = fun _ => none)
    (gen : NameGenerator) (cfg : ErasureConfig) :
    BridgeInv env Us (fun _ => False) Γ gen ⟨{}, none, Us, cfg⟩ {} [] where
  mlc := ⟨.nil, trivial, rfl, rfl⟩
  lparams := rfl
  kfresh := fun _ hfv => nomatch hfv
  fixvars := by intro nm x; rw [hnfv]; simp
  fixfresh := by intro nm x hx; rw [hnfv] at hx; simp at hx
  reserved := fun _ hfv => nomatch hfv
  knames := hkn
  consts := by intro n k hk; simp at hk
  known_dom := fun _ h => h.elim

end LeanToLambdaBox
