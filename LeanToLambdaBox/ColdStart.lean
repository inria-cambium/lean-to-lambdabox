import LeanToLambdaBox.ColdStartDelta
import LeanToLambdaBox.FirstOrderShippingIota

/-!
# The cold-start capstone: the subject becomes `Erasure.erase` (slice S4)

Every capstone so far has taken its subject to be a `visitExpr` run **under an abstract,
already-registered `ErasureState`**, with the environment `E`, the registration records
and the bridge invariant all supplied from outside. This file moves the subject to the
real `#erase` entry point,

```lean
Erasure.erase e cfg cctx ref w = .ok (p, inls) w'
```

from the **empty** state, and produces `E` and `t` rather than consuming them.

## What the walk discharges

Everything below is *derived from the run*, not assumed:

| premise of `…ι_registered` | how it dies |
|---|---|
| the abstract state `s` and the run `visitExpr e s …` | `ColdStartRun.erase_run_ok` (R1) |
| `sp`, the post-`prepare_erasure` state | `ColdStartRun.run_prepare_erasure_state` (R2), csimp off: it *is* `{}` |
| `hinv : BridgeInv …` | constructed at `{}` by `gBridgeInv_nil` |
| `E` as a free variable | becomes `sf.gdecls`, existentially produced |
| `hclenv : ClosedEnv E` | `RegInvShape.closed`, at the run's final state (S1e: carried by `visitExpr_regInvShape`, a theorem) |
| `hcl : LBClosed t 0` | `visitExpr_noFix_closed` (R11, no hypotheses) |
| `hregctors`/`hregcases`/`hregfields` | `RegInvShape.registeredCtors/…`, modulo saturation |
| `hdelta : ErasesEnvDeltaData` | the walk's own δ record, converted (slice D5) |
| `known` as a free variable | stays free — the fragment (slice D5) |

## Scope note: the cold-start fragment used to be δ-free (slices D1–D5)

Every capstone here was pinned at `known = ⊥`, `Esrc = ⊥` until slice D5, and the reason
was one invariant field:

> `BridgeInv.known_dom` said a `known` constant is *already registered*. At the empty state
> nothing is, so the only sound instantiation was `known = ⊥` — and `Supported.const` needs
> `known n`. The cold-start fragment therefore contained no δ-constant: constructors,
> `casesOn` heads, literals, λ, `let` and application, but no plain constant reference.
> Consequently `Esrc` was empty and the δ records (`SEnvConsistent`, `ErasesEnvDeltaData`,
> `RecEnvConsistent`) were discharged *vacuously* rather than from the walk.

The field is gone (D4a, with `visitMutual`'s motive taking its job), the record now travels
the walk (D4b, `DeltaMem`/`RunConclδ`), and this slice (D5) wires the two into the
capstones. What changed here, precisely:

* `known` and `Esrc` are **parameters**. `gBridgeInv_nil` no longer pins `known`, so the
  entry configuration carries the invariant at any fragment.
* `ErasesEnvDeltaData` is **derived**, not assumed: the bridge's `RunConclδ` transports
  `DeltaMem.empty` to the run's final state, and
  `ColdStartDelta.registeredClosureData_of_deltaMem_walked` converts it.
* The conversion is stated at `Esrc.walked Γ sf.gdecls` — `Esrc` cut down to the constants
  the run's environment really stores a body for. That is what makes the *existence* of
  each registration derivable rather than assumed, and it removes the `KeysDistinct`
  (`hkinj`) premise the design expected to pay here; see `SEnv.walked`. The price is that
  the source-evaluation premise is stated at the restricted environment — the honest place
  for "the program only calls what the walk reached".
* Two residues survive, both named and both pre-existing classes: context-uniformity
  (`DeltaHyps.uniform`, a lean4lean-side `TrExprS`-weakening obligation) and applied form
  of the recorded bodies (`ColdStartSubject.noBlockEnv`, an output-shape statement the
  shape induction does not prove).

`SEnvConsistent` is **not** derived and should not be: it says the prepared body is defeq
to the kernel's value for the constant, which is a `PrepareHyps`-class fact about the
elaborator, not about the walk. The δ guard at the end of this file discharges it at a
concrete two-declaration environment, from `VEnv`'s own defining equation.

## The premise ledger, after this slice

* **Proved from the run** — the state, the environment, `ClosedEnv`, `LBClosed t 0`, the
  bridge invariant, the `Program` shape.
* **Runtime Hoare bundles** — `BridgeHyps`, `DataBridgeHyps`, `CasesBridgeHyps`,
  `PrepareHyps` (now three fields: `prepare_sound` is *derived*, see
  `ColdStartRun.prepare_sound_of_prepareHyps`), and `RegBridgeHyps` — which after slice
  S1e no longer carries registry-invariant preservation (that is the theorem
  `ColdStartInduction.visitExpr_regInvShape`) but only the `Γ`-agreement for a cold
  `register_inductive`, the registration completeness, and the `prepare_erasure` trust
  item. `ColdStartInduction.RegShapeHyps` is **not** used — it is refuted below.
* **`Γ`-side conditions** — `hknames` (inside `RegBridgeHyps`), `Γ.fixvars = ⊥`,
  `Γ.recBodies = ⊥`, the peano-config pin, and `Us = []` (universe monomorphism, which at
  the entry point is not a restriction but a *fact*: `Erasure.run` installs
  `lparams := []`, and `BridgeInv.lparams` pins `ctx.lparams = Us`).
* **Certificates** — `IotaConsistent`, `IotaArityCoherent`, `IotaRelevant`, the
  constructor/`casesOn` disjointness; all `rfl`-checkable at a concrete `Γ`.
* **About the subject** — `ColdStartSubject` (the prepared term is supported and
  translatable; the output, and every body the walk recorded, is in applied form) and the
  source evaluation, both stated about `prepare_erasure e` rather than `e`, since that is
  what the run erases.
* **The δ fragment** (slice D5) — `DeltaHyps` (scope side) and `SEnvConsistent` (source
  side). Everything *target*-side about δ is derived.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

/-! ## A refuted premise, and what replaced it

Slice S1d collected the registration-side side conditions of the shape argument in
`ColdStartInduction.RegShapeHyps`, and `visitExpr_regInvShape` carried the registry
invariant through a whole run *given that record*. **The record is inconsistent**, so at
slice S4 those three corollaries (`visitExpr_regInvShape`, `visitMutual_regInvShape`,
`get_constant_kername_regInvShape`) were vacuous and could not discharge anything.

Slice S1e repaired that — see `ColdStartInduction`'s "`RegInvShape` is `RunClosed`"
section — and the corollaries below are the repaired ones, consuming `RegBridgeHyps`. The
refutations stay as the negative guards they always were, and the record they refute stays
with them, unused.

Three independent refutations, all proved below:

* `regShapeHyps_fresh_refuted` — `fresh` quantifies over **every** state satisfying the
  invariant, with no link to the call being made. `RegInvShape Γ (addAxiomState n {})` is
  a *theorem* (S1's own `RegInvShape.addAxiom` at the empty state), and in that state
  `Erasure.toKername n` is already a key, so `fresh` at that state and that name asserts
  `Kername.beq (toKername n) (toKername n) = false`.
* `regShapeHyps_recClosed_refuted` — `recClosed` asserts `LBClosed (.fix defs j) 0` for
  **every** `defs`, and a one-definition block whose body is `.bvar 5` is not closed.

* `regShapeHyps_regCtors_refuted` (slice S1e) — `regCtors` is keyed on a
  `register_inductive` run with no branch guard, and the *hit* branch's run is
  constructible from `run_get`/`run_pure`, so the field can be instantiated at a hand-made
  state whose `gdecls` is empty. `regKeys`/`regCases`/`regFields` fall the same way.

### What the repair turned out to be (slice S1e)

The repair spec written here at S4 was right about the two moving parts and wrong about
the diagnosis. Both parts landed:

1. a **coverage** field in `RegInvShape` (`ConstKeysCovered`), which needed
   `Erasure.run_register_inductive_cold_ok`'s `ConstExt` to record the *keys* of its
   `@[extern]`-constructor axiom prefix — it now does;
2. `RunClosed.rc` **takes** the closedness of the block it is storing, supplied by
   `Erasure.run_rec_exit_ok` from `run_mkDef_ok` plus the binder-fold arithmetic.

But coverage does not restore key *distinctness*, and no side condition could:
`ColdStartInduction.runClosed_keysDistinct_refuted` shows a `RunClosed` predicate cannot
contain `KeysDistinct` at all, because `nrc` is a bare state closure. So `RegInvShape`'s
`keys` field is gone, coverage stands in its place, and the freshness the design called
`hkinj` is now a *derived* fact for a not-yet-registered name
(`RegInvShape.fresh_of_unregistered`) rather than a premise.

With that, `visitExpr_regInvShape` is a theorem again and S4's `RegBridgeHyps.regInv`
field — which stated its conclusion, keyed on a run, to route around the vacuity — is
gone. What remains in `RegBridgeHyps` is what `Γ` being a parameter really costs: the
naming convention, the `Γ`-agreement for a cold `register_inductive`, the completeness
facts, and the `prepare_erasure` trust item. -/

/-- **`RegShapeHyps` is inconsistent (i).** Its `fresh` field, instantiated at the state
S1's own `RegInvShape.addAxiom` produces, asserts that a kername differs from itself. -/
theorem regShapeHyps_fresh_refuted {Γ : ErasureCtx} (Hg : RegShapeHyps Γ) : False := by
  have hinv : RegInvShape Γ (addAxiomState `x {}) :=
    (RegInvShape.empty Γ).addAxiom (Hg.knames `x)
  have := Hg.fresh (n := `x) hinv (toKername `x, .constantDecl ⟨none⟩) (by simp [addAxiomState])
  simp at this

/-- **`RegShapeHyps` is inconsistent (ii)** — independently of (i). `recClosed` ranges
over *every* block, including one whose single body is a loose de Bruijn index. -/
theorem regShapeHyps_recClosed_refuted {Γ : ErasureCtx} (Hg : RegShapeHyps Γ) : False := by
  have := Hg.recClosed [{ name := .anon, body := .bvar 5 }] 0
  simp [LBClosedDefs] at this

/-! ### …and (iii): the unguarded `register_inductive` fields

Slice S4 asserted this one without formalising it; slice S1e formalises it, because it is
what forces the cold guard in the repaired bundle. A one-name inductive, a state that
already knows it (so the call takes the *hit* branch and returns unchanged), and an empty
`gdecls`: `Erasure.run_register_inductive_hit_mk` builds that run out of `get`/`pure`
alone, and `regCtors` then claims a block registration in the empty environment.

Note the `Γ` here records a constructor — which is the point. At a `Γ` with no
constructors these fields are vacuous, so the refutation needs (and uses) the only kind of
`Γ` the capstone is interesting at. -/

/-- A one-name inductive, for the hit-branch instantiation. -/
private def gIIref : InductiveVal where
  name := `I
  levelParams := []
  type := .sort .zero
  numParams := 0
  numIndices := 0
  all := [`I]
  ctors := []
  numNested := 0
  isRec := false
  isUnsafe := false
  isReflexive := false

private def gIidRef : InductiveId := ⟨mutualBlockKn gIIref, 0⟩

/-- A `Γ` that records a constructor of `gIIref`'s block — a `Γ` of the shape the capstone
is stated at, not a degenerate one. -/
private def gΓind : ErasureCtx where
  inductives := fun _ => none
  constants := toKername
  ctors := fun _ => some (gIidRef, 0)
  ctorArities := fun _ => none
  casesOns := fun _ => none

/-- **`RegShapeHyps` is inconsistent (iii).** `regCtors` is keyed on a `register_inductive`
run with no branch guard, and the hit branch's run is constructible; at a state that knows
the block but has an empty `gdecls`, it asserts a registration that is not there.
`regKeys`/`regCases`/`regFields` fall the same way. -/
theorem regShapeHyps_regCtors_refuted (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld)
    (Hg : RegShapeHyps gΓind) : False := by
  have hhit : ({ ({} : ErasureState) with
      inductives := (∅ : Std.HashMap Name (InductiveId × InductiveArgMasks)).insert
        gIIref.name (gIidRef, default) } : ErasureState).inductives.get? gIIref.name
      = some (gIidRef, default) := by
    simp
  have hrun := Erasure.run_register_inductive_hit_mk (ctx := ctx) (cctx := cctx)
    (ref := ref) (w := w) hhit
  obtain ⟨body, oib, cb, hlk, -⟩ :=
    Hg.regCtors hrun (cn := `c) (iid := gIidRef) (cidx := 0) (by simp [gIidRef]) rfl
  simp [LBTerm.envLookup] at hlk

/-! ## The subject bundle

`Erasure.erase` runs `visitExpr (← prepare_erasure e)`, so every fact a capstone needs
about "the term being erased" is a fact about the **prepared** term, which the run
produces and the statement cannot name. They are collected here, each quantified over the
prepare run that produces it.

`PrepareHyps.prepare_sound` is what relates the prepared term's source evaluation back to
`e`'s; it is stated for `SEvalData`, so the `SEvalDataι`/`SEvalDataC` flavours the
capstones use are taken directly about the prepared term. -/
structure ColdStartSubject (env : VEnv) (Us : List Name) (known : Name → Prop)
    (Γ : ErasureCtx) (e : Expr) (cfg : ErasureConfig) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) : Prop where
  /-- The prepared term is in the supported fragment — since slice D5 at an **arbitrary**
  fragment `known`, so the subject may reference constants; before D5 the only sound
  instantiation was `known = ⊥`, and the reason is the module docstring's scope note.
  Read this in one breath with `DeltaHyps.prepared`, which is the *same* premise for the
  subject's callees. -/
  supported : ∀ {pe : Expr} {s₁ : ErasureState} {w₁ : Void IO.RealWorld},
    Erasure.prepare_erasure e {} { «config» := cfg } cctx ref w = .ok (pe, s₁) w₁ →
    Supported known Γ pe ∧ ∃ ve, TrExprS env Us [] pe ve
  /-- The erased term is in applied (`NoBlock`) form — the data fragment's shape premise,
  here about the entry point's own run. -/
  noBlock : ∀ {pe : Expr} {sp : ErasureState} {wp : Void IO.RealWorld} {t : LBTerm}
      {sf : ErasureState} {wt : Void IO.RealWorld},
    Erasure.visitExpr pe sp { «config» := cfg } cctx ref wp = .ok (t, sf) wt → NoBlock t
  /-- **…and so is every body the walk recorded on the way** (slice D5) — the applied-form
  residue of the δ record, in the only shape available at the capstone.

  It is the same statement as `noBlock` one level down, and it stays a premise for the
  same reason: `NoBlock` is an output-shape fact about `visitExpr`, the shape induction
  proves `NoFix`/`LBClosed` and not it (`ColdStartInduction.visitExpr_regInvShape`), and
  inside the bridge the erasure argument is abstract, so no motive can conclude it either.
  Note it is stated about the run's final *environment* rather than about a dependency's
  own run: at the capstone a `gdecls` entry does not come with the run that produced it,
  and manufacturing that link is a separate walk fact this slice does not build. -/
  noBlockEnv : ∀ {pe : Expr} {sp : ErasureState} {wp : Void IO.RealWorld} {t : LBTerm}
      {sf : ErasureState} {wt : Void IO.RealWorld},
    Erasure.visitExpr pe sp { «config» := cfg } cctx ref wp = .ok (t, sf) wt →
    NoBlockEnv sf.gdecls

/-! ## The capstone -/

/--
**Cold-start D3ι — the shipping eraser, from the entry point.** For a source `e` whose
prepared form is supported, lean4lean-translatable and `SEvalDataι`-evaluates to a
first-order value `v`: a successful `Erasure.erase e cfg` (csimp off) returns
`Program.untyped E (some t)` for an environment `E` and a term `t` **it built itself**,
and `t` `WcbvEval`-uates at `appliedFlags` to *the* unique applied-form erasure of `v`.

No `ErasureState`, no `E`, no registration record and no bridge invariant is supplied
from outside: they are produced by `ColdStartRun.erase_run_ok` (R1),
`ColdStartRun.run_prepare_erasure_state` (R2), `ColdStartShape.RegInvShape.empty` and
`ColdStartInduction.visitExpr_regInvShape`. What survives is documented in the module
docstring's ledger.
-/
theorem shipping_erase_correct_firstorderι_coldstart
    {env : VEnv} (henv : env.WF) {Us : List Name} (hUs : Us = [])
    {known : Name → Prop} {Γ : ErasureCtx} {Esrc : SEnv}
    {ia : IotaArities} {cfg : ErasureConfig} (hcsimp : cfg.csimp = false)
    -- Γ-side conditions
    (hnfv : Γ.fixvars = fun _ => none) (hnorec : Γ.recBodies = fun _ => none)
    (hnat : Γ.natPeano = true → cfg.nat = .peano)
    -- registration bundle
    (Hr : RegBridgeHyps Γ)
    -- the source-side δ trust item (see the ledger: it cannot come from the walk)
    (hcon : SEnvConsistent env Us Esrc)
    -- ι certificates
    (hiota : IotaConsistent env Us Γ ia)
    (hiacoh : IotaArityCoherent Γ ia)
    (hrel : IotaRelevant env Us Γ)
    (hcc : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
             Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none)
    -- runtime Hoare bundles
    {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps env Us known Γ Esrc gw cc rf)
    -- the subject
    {e v : Expr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld}
    (S : ColdStartSubject env Us known Γ e cfg cctx ref w)
    (hev : ∀ {pe : Expr} {sp sf : ErasureState} {wp wt : Void IO.RealWorld} {t : LBTerm},
      Erasure.prepare_erasure e {} { «config» := cfg } cctx ref w = .ok (pe, sp) wp →
      Erasure.visitExpr pe sp { «config» := cfg } cctx ref wp = .ok (t, sf) wt →
      SEvalDataι Γ ia (Esrc.walked Γ sf.gdecls) pe v)
    (hfo : FirstOrderValue env Us Γ [] v)
    -- the run: the REAL entry point, cold
    {p : Program} {inls : List Kername} {w' : Void IO.RealWorld}
    (hrun : Erasure.erase e cfg cctx ref w = .ok (p, inls) w') :
    ∃ (E : GlobalDeclarations) (t t' : LBTerm),
      p = .untyped E (some t) ∧
      WcbvEval E appliedFlags t t' ∧
      (∃ vve, TrExprS env Us [] v vve) ∧
      Erases env Us Γ [] v t' ∧ NoBlock t' ∧ LBClosed t' 0 ∧
      ∀ tu, Erases env Us Γ [] v tu → NoBlock tu → tu = t' := by
  subst hUs
  -- R1: the entry point decomposes into the two runs, from the empty state.
  obtain ⟨pe, t, sp, sf, wp, wt, hpr, hvis, hp, -⟩ := erase_run_ok hrun
  -- R2: with csimp off, `prepare_erasure` does not touch the state, so `sp = {}`.
  obtain rfl : sp = {} := run_prepare_erasure_state (by simpa using hcsimp) hpr
  -- The registry invariant starts vacuously true and survives the run.
  have hshape : RegInvShape Γ sf := (visitExpr_regInvShape Hr hvis (RegInvShape.empty Γ)).1
  have hcl : LBClosed t 0 := (visitExpr_noFix_closed hvis).2
  -- The bridge invariant is *constructed* at the entry configuration.
  have hinv : BridgeInv env [] known Γ (gw wp) { «config» := cfg } {} [] :=
    gBridgeInv_nil env [] known Γ Hr.knames hnfv (gw wp) cfg hnat
  obtain ⟨hsup, hex⟩ := S.supported hpr
  obtain ⟨ve, htr⟩ := hex
  -- D5: the δ record the walk carried, at the run's final state. `DeltaMem.empty` is the
  -- entry-state instance (nothing is recorded yet), and the bridge's `RunConclδ` — the
  -- state-side conclusion every motive carries since D4b — transports it to `sf`.
  have hmem : DeltaMem env [] Γ Esrc sf :=
    (visitExpr_refines_erases H HD C Hδ henv.ordered pe {} { «config» := cfg } cctx ref wp
      t sf wt hvis [] hinv hsup ⟨ve, htr⟩).2.1.δ DeltaMem.empty
  -- …converted, at the walk-restricted source environment, into the record the data
  -- simulation consumes. Existence and key distinctness are *by construction* of
  -- `SEnv.walked`; `hdisj` is the fragment's own δ-closure clause; the two residues are
  -- `DeltaHyps.uniform` and the subject bundle's `noBlockEnv`.
  have hdelta : ErasesEnvDeltaData env [] Γ (Esrc.walked Γ sf.gdecls) sf.gdecls :=
    erasesEnvDeltaData_of_registeredClosureData
      (registeredClosureData_of_deltaMem_walked hmem
        (fun hb => (Hδ cctx ref).disj ((Hδ cctx ref).esrc_sub (by rw [hb]; simp)))
        (fun hb _ her => (Hδ cctx ref).uniform hb her) (S.noBlockEnv hvis))
  obtain ⟨t', heval, htrv, herv, hnbv, hclv, huniq⟩ :=
    shipping_erase_correct_firstorderι henv (Us := [])
      (Esrc := Esrc.walked Γ sf.gdecls) (E := sf.gdecls) (known := known)
      hcon.walked
      hiota
      hdelta
      (erasesEnvCtor_of_registeredCtors (hshape.registeredCtors (Hr.satCtors hvis)))
      (erasesEnvCases_of_registeredCases (hshape.registeredCases (Hr.satCases hvis)))
      (ctorFieldsCoherent_of_registered (hshape.registeredCtors (Hr.satCtors hvis))
        (hshape.registeredCases (Hr.satCases hvis))
        (hshape.registeredCtorFieldsAll (Hr.satCases hvis)))
      hiacoh hrel hcc (recEnvConsistent_of_noRec hnorec) hnfv hshape.closed H HD C Hδ
      hvis hinv hsup htr (S.noBlock hvis) hcl (hev hpr hvis) hfo
  exact ⟨sf.gdecls, t, t', hp, heval, htrv, herv, hnbv, hclv, huniq⟩

/-- **Cold-start D3 — the βζδ+data flavour.** Same composition, with the source
evaluation at `SEvalDataC` (β + δ + saturated constructors) and the ι certificate block
dropped; it goes through `shipping_erase_correct_firstorder`, whose conclusion carries no
`LBClosed t'`. The two flavours differ only in which capstone they call, which is what
"the composition is uniform" means here. -/
theorem shipping_erase_correct_firstorder_coldstart
    {env : VEnv} (henv : env.WF) {Us : List Name} (hUs : Us = [])
    {known : Name → Prop} {Γ : ErasureCtx} {Esrc : SEnv}
    {cfg : ErasureConfig} (hcsimp : cfg.csimp = false)
    (hnfv : Γ.fixvars = fun _ => none) (hnorec : Γ.recBodies = fun _ => none)
    (hnat : Γ.natPeano = true → cfg.nat = .peano)
    (Hr : RegBridgeHyps Γ)
    (hcon : SEnvConsistent env Us Esrc)
    (hcc : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
             Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none)
    {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps env Us known Γ Esrc gw cc rf)
    {e v : Expr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld}
    (S : ColdStartSubject env Us known Γ e cfg cctx ref w)
    (hev : ∀ {pe : Expr} {sp sf : ErasureState} {wp wt : Void IO.RealWorld} {t : LBTerm},
      Erasure.prepare_erasure e {} { «config» := cfg } cctx ref w = .ok (pe, sp) wp →
      Erasure.visitExpr pe sp { «config» := cfg } cctx ref wp = .ok (t, sf) wt →
      SEvalDataC Γ (Esrc.walked Γ sf.gdecls) pe v)
    (hfo : FirstOrderValue env Us Γ [] v)
    {p : Program} {inls : List Kername} {w' : Void IO.RealWorld}
    (hrun : Erasure.erase e cfg cctx ref w = .ok (p, inls) w') :
    ∃ (E : GlobalDeclarations) (t t' : LBTerm),
      p = .untyped E (some t) ∧
      WcbvEval E appliedFlags t t' ∧
      (∃ vve, TrExprS env Us [] v vve) ∧
      Erases env Us Γ [] v t' ∧ NoBlock t' ∧
      ∀ tu, Erases env Us Γ [] v tu → NoBlock tu → tu = t' := by
  subst hUs
  obtain ⟨pe, t, sp, sf, wp, wt, hpr, hvis, hp, -⟩ := erase_run_ok hrun
  obtain rfl : sp = {} := run_prepare_erasure_state (by simpa using hcsimp) hpr
  have hshape : RegInvShape Γ sf := (visitExpr_regInvShape Hr hvis (RegInvShape.empty Γ)).1
  have hinv : BridgeInv env [] known Γ (gw wp) { «config» := cfg } {} [] :=
    gBridgeInv_nil env [] known Γ Hr.knames hnfv (gw wp) cfg hnat
  obtain ⟨hsup, ve, htr⟩ := S.supported hpr
  have hmem : DeltaMem env [] Γ Esrc sf :=
    (visitExpr_refines_erases H HD C Hδ henv.ordered pe {} { «config» := cfg } cctx ref wp
      t sf wt hvis [] hinv hsup ⟨ve, htr⟩).2.1.δ DeltaMem.empty
  have hdelta : ErasesEnvDeltaData env [] Γ (Esrc.walked Γ sf.gdecls) sf.gdecls :=
    erasesEnvDeltaData_of_registeredClosureData
      (registeredClosureData_of_deltaMem_walked hmem
        (fun hb => (Hδ cctx ref).disj ((Hδ cctx ref).esrc_sub (by rw [hb]; simp)))
        (fun hb _ her => (Hδ cctx ref).uniform hb her) (S.noBlockEnv hvis))
  obtain ⟨t', heval, htrv, herv, hnbv, huniq⟩ :=
    shipping_erase_correct_firstorder henv (Us := [])
      (Esrc := Esrc.walked Γ sf.gdecls) (E := sf.gdecls) (known := known)
      hcon.walked
      hdelta
      (erasesEnvCtor_of_registeredCtors (hshape.registeredCtors (Hr.satCtors hvis)))
      hcc (recEnvConsistent_of_noRec hnorec) hnfv H HD C Hδ
      hvis hinv hsup htr (S.noBlock hvis) (hev hpr hvis) hfo
  exact ⟨sf.gdecls, t, t', hp, heval, htrv, herv, hnbv, huniq⟩

/-! ## Non-vacuity guards

### What is constructible here, and what is not

The obstructions are the ones every capstone guard in this development already carries,
plus one that is specific to the entry point:

* **the run** — no successful run of the erasure family is constructible in-logic (every
  branch passes through opaque `CoreM`/`MetaM` primitives and needs a real
  `ST.Ref`/world token), so `hrun` stays hypothetical, exactly as in the D3/D3ι guards;
* **the four runtime bundles** `H`/`HD`/`C`/`Hr` and the two ι trust items
  (`IotaConsistent`, `IotaRelevant`) — same discipline;
* **the prepared subject** (`ColdStartSubject`, `hev`) — *new here*, and unavoidable: the
  entry point erases `prepare_erasure e`, which is the output of three opaque elaborator
  transforms, so nothing about it can be computed. This is the entry point's own version
  of the `NoBlock t` premise the warm guards already leave hypothetical.

Everything `Γ`-level is constructed, at the same `ΓFOι`/`iaFOι` pin the warm ι guard
uses: the fixvar and recursion exclusions, the peano-config pin, `IotaArityCoherent`,
the constructor/`casesOn` disjointness, and the value's first-orderness. -/

/-- **The cold-start capstone fires.** At the registered inductive of the ι guard, on a
source whose prepared form evaluates to the first-order constructor `c`: `Erasure.erase`
returns a `Program` whose term reaches *the* unique applied-form erasure of `c`, in an
environment the run built. Hypothetical: the run, the four bundles, the two ι trust
items, and the prepared-subject facts — see the section docstring. -/
example (harity : ¬ IsArityUpTo envFO 0 [] (.const `I []))
    (cfg : ErasureConfig) (hcsimp : cfg.csimp = false)
    (hiota : IotaConsistent envFO [] ΓFOι iaFOι) (hrel : IotaRelevant envFO [] ΓFOι)
    (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps envFO [] ΓFOι gw) (HD : DataBridgeHyps ΓFOι gw)
    (C : CasesBridgeHyps ΓFOι gw) (Hr : RegBridgeHyps ΓFOι)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps envFO [] (fun _ => False) ΓFOι (fun _ => none) gw cc rf)
    {e : Expr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {p : Program} {inls : List Kername}
    (S : ColdStartSubject envFO [] (fun _ => False) ΓFOι e cfg cctx ref w)
    (hev : ∀ {pe : Expr} {s₁ : ErasureState} {w₁ : Void IO.RealWorld},
      Erasure.prepare_erasure e {} { «config» := cfg } cctx ref w = .ok (pe, s₁) w₁ →
      SEvalDataι ΓFOι iaFOι (fun _ => none) pe (.const `c []))
    (hrun : Erasure.erase e cfg cctx ref w = .ok (p, inls) w') :
    ∃ (E : GlobalDeclarations) (t t' : LBTerm),
      p = .untyped E (some t) ∧
      WcbvEval E appliedFlags t t' ∧
      (∃ vve, TrExprS envFO [] [] (.const `c []) vve) ∧
      Erases envFO [] ΓFOι [] (.const `c []) t' ∧ NoBlock t' ∧ LBClosed t' 0 ∧
      ∀ tu, Erases envFO [] ΓFOι [] (.const `c []) tu → NoBlock tu → tu = t' :=
  shipping_erase_correct_firstorderι_coldstart envFO_wf rfl hcsimp rfl rfl
    (by simp [ΓFOι]) Hr (by intro Δ n us body cve h; exact absurd h (by simp))
    hiota ΓFOι_iotaArityCoherent hrel ΓFOι_cc H HD C Hδ S
    (fun hp _ => by rw [SEnv.walked_bot]; exact hev hp)
    (envFO_foC_ι harity) hrun

/-- The βζδ+data flavour of the same guard, at the same pin. -/
example (harity : ¬ IsArityUpTo envFO 0 [] (.const `I []))
    (cfg : ErasureConfig) (hcsimp : cfg.csimp = false)
    (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps envFO [] ΓFOι gw) (HD : DataBridgeHyps ΓFOι gw)
    (C : CasesBridgeHyps ΓFOι gw) (Hr : RegBridgeHyps ΓFOι)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps envFO [] (fun _ => False) ΓFOι (fun _ => none) gw cc rf)
    {e : Expr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {p : Program} {inls : List Kername}
    (S : ColdStartSubject envFO [] (fun _ => False) ΓFOι e cfg cctx ref w)
    (hev : ∀ {pe : Expr} {s₁ : ErasureState} {w₁ : Void IO.RealWorld},
      Erasure.prepare_erasure e {} { «config» := cfg } cctx ref w = .ok (pe, s₁) w₁ →
      SEvalDataC ΓFOι (fun _ => none) pe (.const `c []))
    (hrun : Erasure.erase e cfg cctx ref w = .ok (p, inls) w') :
    ∃ (E : GlobalDeclarations) (t t' : LBTerm),
      p = .untyped E (some t) ∧
      WcbvEval E appliedFlags t t' ∧
      (∃ vve, TrExprS envFO [] [] (.const `c []) vve) ∧
      Erases envFO [] ΓFOι [] (.const `c []) t' ∧ NoBlock t' ∧
      ∀ tu, Erases envFO [] ΓFOι [] (.const `c []) tu → NoBlock tu → tu = t' :=
  shipping_erase_correct_firstorder_coldstart envFO_wf rfl hcsimp rfl rfl
    (by simp [ΓFOι]) Hr (by intro Δ n us body cve h; exact absurd h (by simp))
    ΓFOι_cc H HD C Hδ S (fun hp _ => by rw [SEnv.walked_bot]; exact hev hp)
    (envFO_foC_ι harity) hrun

/-! ## The δ guard: a program that CALLS a walked function (slice D5)

The two guards above are the *old* ones, re-checked at the new statement: their fragment
is still `known = ⊥`, so they exercise the rewiring but not the δ. This section is the one
the slice exists for — **a two-declaration source**, `g := c` and a program that calls `g`.

### Where it fires, and where it cannot

At the **cold-start** entry point the subject is `prepare_erasure e`, the output of three
opaque elaborator transforms, so `pe` cannot be named and the source evaluation premise is
hypothetical whatever the fragment is. What the cold-start guard can therefore show — and
does, last in this section — is that the capstone's *statement* is now instantiable at a
genuinely non-empty fragment: `known` holds of `g`, `Esrc` records its body, the bridge
invariant is constructed at the empty state at that fragment (`gBridgeInv_nil`, `known` no
longer pinned at `⊥`), and the δ record is *derived* from the walk.

The δ **step** is exercised one level down, at the warm capstone, whose subject can be
named: `shipping_erase_correct_firstorder` on the program `.const g []`. There the source
evaluation really takes `SEvalDataC.delta`, and `ErasesEnvDeltaData` — the premise that
lets the *target* take its matching `WcbvEval` δ step — is produced by D5's conversion out
of a `DeltaMem`, not assumed. That pair is the whole point of δ-inclusion.

### What is constructed and what is not

Constructed: the environment (a real *definition* `g : I := c`, so `SEnvConsistent` is
discharged from `VEnv`'s own defining equation rather than assumed — the first time in this
development that premise is met at a non-empty `Esrc`), its well-formedness, the fragment,
the `Supported.const` derivation, the bridge invariant, the δ record and its walk
restriction, the source evaluation's δ step, and the value's first-orderness.

Hypothetical, all pre-existing classes: the run; the four runtime bundles; `NoBlock t`
(a statement about the run's output); and `harity` — the single lean4lean-blocked side
condition `FirstOrder.lean` documents, here restated at this environment. -/

section DeltaGuard

/-- The two-declaration environment's new declaration: **a definition**, `g : I := c`.
`VDecl.WF.def` is what turns it into a `VEnv` defining equation (`VDefVal.toDefEq`), and
that equation is what `SEnvConsistent` needs — a δ step is a *defeq*, so a fragment
constant has to be a `def`, not an axiom. -/
def gDefδ : VDefVal := ⟨⟨⟨0, .const `I []⟩, `g⟩, .const `c []⟩

/-- `envFO` (`I : Sort 1`, `c : I`) extended with the constant `g : I`. -/
noncomputable def envδ0 : VEnv := (envFO.addConst `g gDefδ.toVConstant).getD .empty

/-- …and with `g`'s defining equation `g ≡ c : I`. -/
noncomputable def envδ : VEnv := envδ0.addDefEq gDefδ.toDefEq

theorem envδ_addg : envFO.addConst `g gDefδ.toVConstant = some envδ0 := by
  unfold envδ0 gDefδ envFO VEnv.addConst VEnv.empty; simp

theorem envδ_g : envδ.constants `g = some ⟨0, .const `I []⟩ := by
  unfold envδ envδ0 gDefδ envFO VEnv.addDefEq VEnv.addConst VEnv.empty; simp
theorem envδ_c : envδ.constants `c = some ⟨0, .const `I []⟩ := by
  unfold envδ envδ0 gDefδ envFO VEnv.addDefEq VEnv.addConst VEnv.empty; simp
theorem envδ_I : envδ.constants `I = some ⟨0, .sort (.succ .zero)⟩ := by
  unfold envδ envδ0 gDefδ envFO VEnv.addDefEq VEnv.addConst VEnv.empty; simp

/-- The environment is well-formed: `envFO`'s two axioms, then one `def` whose value is
typed by `envFO_cTypeI`. -/
theorem envδ_wf : envδ.WF := by
  obtain ⟨ds, hds⟩ := envFO_wf
  exact ⟨.def gDefδ :: ds, .decl (.def envFO_cTypeI envδ_addg) hds⟩

/-- `.const g []` translates (nullary constant). -/
theorem envδ_trG : TrExprS envδ [] [] (.const `g []) (.const `g []) :=
  .const envδ_g (by simp) (by simp)

/-- **The defining equation, as a defeq at every context.** `VEnv.IsDefEq.extra` is
context-polymorphic, which is exactly what `SEnvConsistent`'s `∀ Δ` needs. -/
theorem envδ_gc (Γ : List VExpr) : envδ.IsDefEqU 0 Γ (.const `g []) (.const `c []) := by
  refine ⟨.const `I [], ?_⟩
  have h : envδ.defeqs gDefδ.toDefEq := Or.inl rfl
  have hx := VEnv.IsDefEq.extra (env := envδ) (uvars := 0) (Γ := Γ) (ls := []) h
    (by simp) rfl
  simpa [gDefδ, VDefVal.toDefEq, VLevel.params, VExpr.instL] using hx

/-- The fragment: `g` and nothing else. -/
def knownδ : Name → Prop := fun n => n = `g

/-- The source environment: `g` unfolds to the nullary constructor `c`. -/
def Esrcδ : SEnv := fun n => if n = `g then some (.const `c []) else none

@[simp] theorem Esrcδ_g : Esrcδ `g = some (.const `c []) := by simp [Esrcδ]

theorem Esrcδ_eq {n : Name} {body : Expr} (h : Esrcδ n = some body) :
    n = `g ∧ body = .const `c [] := by
  by_cases hn : n = `g
  · exact ⟨hn, by simpa [Esrcδ, hn] using h.symm⟩
  · simp [Esrcδ, hn] at h

/-- **`SEnvConsistent` at a non-empty `Esrc`, discharged.** The source-side δ trust item
of every capstone, met here from the environment's own defining equation instead of being
assumed vacuously. -/
theorem envδ_senvConsistent : SEnvConsistent envδ [] Esrcδ := by
  intro Δ n us body cve hb htr
  obtain ⟨rfl, rfl⟩ := Esrcδ_eq hb
  cases htr with
  | const hci hus hlen =>
    rw [envδ_g] at hci
    obtain rfl : us = [] := by
      refine List.eq_nil_of_length_eq_zero ?_
      rw [hlen, ← Option.some.inj hci]
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hus
    subst hus
    exact ⟨.const `c [], .const envδ_c (by simp) (by simp), envδ_gc _⟩

/-- The target environment the walk would build for this fragment: `EFOd`'s inductive
block, plus the body it recorded for `g` — the applied-form nullary constructor. -/
def tδ : LBTerm := .construct ⟨toKername `I, 0⟩ 0 []
def Eδ : GlobalDeclarations := (toKername `g, .constantDecl ⟨some tδ⟩) :: EFOd

/-- The state the walk ends in, as far as this record is concerned. -/
def sδ : ErasureState := { ({} : ErasureState) with gdecls := Eδ }

/-- **The δ record, on this fragment.** `Erases.ctor_head` — the applied-form
constructor leaf, which carries no typing premise — is the witness, at *every* `Δ`, so
`DeltaMem`'s `∃ Δ` is met without any residue. -/
theorem gDeltaMemδ : DeltaMem envδ [] ΓFOd Esrcδ sδ where
  erase := by
    intro n body t hb hm
    obtain ⟨rfl, rfl⟩ := Esrcδ_eq hb
    obtain rfl : t = tδ := by
      simp only [sδ, Eδ, EFOd, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h
      · simpa [ΓFOd] using (by simpa using h : ΓFOd.constants `g = toKername `g ∧ t = tδ).2
      · exact absurd h (by simp)
    exact ⟨[], .ctor_head `c [] _ 0 ΓFOd_ctorsC⟩

/-- **The walk restriction keeps the fragment.** `g`'s body really is stored in `Eδ`, so
`SEnv.walked` does not quietly empty `Esrc` — the guard against the restriction being a
vacuity dressed as a derivation. -/
@[simp] theorem Esrcδ_walked_g : Esrcδ.walked ΓFOd Eδ `g = some (.const `c []) := by
  unfold SEnv.walked
  rw [show LBTerm.envLookup Eδ (ΓFOd.constants `g) = some (.constantDecl ⟨some tδ⟩) from
    by simp [Eδ, ΓFOd]]
  simp

/-- **The δ record becomes `ErasesEnvDeltaData`, from the walk.** Every premise of the D5
conversion is discharged here: `hdisj` off `ΓFOd`, `huni` off `Erases.ctor_head`'s
context-polymorphism, `hnb` off the stored body's shape — and existence and key
distinctness are gone by construction of `SEnv.walked`. -/
theorem gErasesEnvDeltaDataδ :
    ErasesEnvDeltaData envδ [] ΓFOd (Esrcδ.walked ΓFOd Eδ) Eδ :=
  erasesEnvDeltaData_of_registeredClosureData
    (registeredClosureData_of_deltaMem_walked (s := sδ) gDeltaMemδ
      (fun hb => by obtain ⟨rfl, rfl⟩ := Esrcδ_eq hb; exact ⟨by simp [ΓFOd], rfl⟩)
      (fun hb hm _ => by
        obtain ⟨rfl, rfl⟩ := Esrcδ_eq hb
        obtain rfl : _ = tδ := by
          simp only [sδ, Eδ, EFOd, List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with h | h
          · exact (by simpa using h : ΓFOd.constants `g = toKername `g ∧ _ = tδ).2
          · exact absurd h (by simp)
        exact .ctor_head `c [] _ 0 ΓFOd_ctorsC)
      (by
        intro kn t hm
        simp only [sδ, Eδ, EFOd, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with h | h
        · obtain rfl : t = tδ := (by simpa using h : kn = toKername `g ∧ t = tδ).2
          simp [tδ]
        · exact absurd h (by simp)))

/-- **The source program δ-unfolds.** `.const g []` evaluates, through
`SEvalDataC.delta`, to the constructor value `c` — at the *walk-restricted* environment,
which is the one the capstone's premise is stated at. -/
theorem gSEvalδ : SEvalDataC ΓFOd (Esrcδ.walked ΓFOd Eδ) (.const `g []) (.const `c []) := by
  refine .delta Esrcδ_walked_g ?_
  have heq : (.const `c [] : Expr) = ([] : List Expr).foldl Expr.app (.const `c []) := rfl
  rw [heq]
  exact .ctor_val ΓFOd_ctorsC ΓFOd_ctorAritiesC (by simp) rfl (fun i h => absurd h (by simp))

/-- `.const c []` is a first-order value at `envδ` — `envFO`'s argument, restated at the
extended environment (the extension adds a constant and a defeq; neither disturbs `I`'s
sort or `c`'s type). -/
theorem envδ_foC_d (harity : ¬ IsArityUpTo envδ 0 [] (.const `I [])) :
    FirstOrderValue envδ [] ΓFOd [] (.const `c []) := by
  have hcT : envδ.HasType 0 [] (.const `c []) (.const `I []) :=
    VEnv.IsDefEq.constDF (env := envδ) (uvars := 0) (Γ := []) (c := `c)
      (ci := ⟨0, .const `I []⟩) (ls := []) (ls' := []) envδ_c
      (by simp) (by simp) (by simp) (by simp)
  have hIT : envδ.HasType 0 [] (.const `I []) (.sort (.succ .zero)) :=
    VEnv.IsDefEq.constDF (env := envδ) (uvars := 0) (Γ := []) (c := `I)
      (ci := ⟨0, .sort (.succ .zero)⟩) (ls := []) (ls' := []) envδ_I
      (by simp) (by simp) (by simp) (by simp)
  have hnp : ¬ envδ.HasType 0 [] (.const `I []) (.sort .zero) := by
    intro h
    have huniq : envδ.IsDefEqU 0 [] (.sort .zero) (.sort (.succ .zero)) :=
      VEnv.IsDefEq.uniqU envδ_wf trivial h hIT
    have := VEnv.IsDefEqU.sort_inv envδ_wf trivial huniq
    rw [VLevel.equiv_def] at this; have := this []; simp [VLevel.eval] at this
  have heq : (.const `c [] : Expr) = ([] : List Expr).foldl Expr.app (.const `c []) := rfl
  rw [heq]
  exact .ctor `c [] ⟨toKername `I, 0⟩ 0 ΓFOd_ctorsC ΓFOd_casesC
    ⟨.const `c [], .const `I [], .const envδ_c (by simp) (by simp), hcT, hnp, harity⟩
    (fun i h => absurd h (by simp))

/-- **The payoff.** The warm D3 capstone, on the program `.const g []` — a program whose
*only* content is a call to another declaration. The source side δ-unfolds
(`SEvalDataC.delta`, `gSEvalδ`); the target side has the matching environment entry,
produced by D5's conversion out of the walk's own record (`gErasesEnvDeltaDataδ`); and the
constant reference is `Supported` because the fragment is non-empty — the derivation
`known = ⊥` used to kill.

Hypothetical: the run, the four bundles, `NoBlock t`, and `harity`. Everything else is
constructed, including the two premises that were previously discharged *vacuously* at
every cold-start capstone (`SEnvConsistent`, `ErasesEnvDeltaData`). -/
example (harity : ¬ IsArityUpTo envδ 0 [] (.const `I []))
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps envδ [] ΓFOd gw) (HD : DataBridgeHyps ΓFOd gw)
    (C : CasesBridgeHyps ΓFOd gw)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps envδ [] knownδ ΓFOd Esrcδ gw cc rf)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w w' : Void IO.RealWorld) (t : LBTerm) (s' : ErasureState)
    (hrun : Erasure.visitExpr (.const `g []) {} ⟨{}, none, [], cfg⟩ cctx ref w
      = .ok (t, s') w')
    (hnb : NoBlock t) :
    ∃ t', WcbvEval Eδ appliedFlags t t' ∧
      (∃ vve, TrExprS envδ [] [] (.const `c []) vve) ∧
      Erases envδ [] ΓFOd [] (.const `c []) t' ∧ NoBlock t' ∧
      ∀ tu, Erases envδ [] ΓFOd [] (.const `c []) tu → NoBlock tu → tu = t' :=
  shipping_erase_correct_firstorder envδ_wf (Us := [])
    (Esrc := Esrcδ.walked ΓFOd Eδ) (E := Eδ) (known := knownδ)
    envδ_senvConsistent.walked gErasesEnvDeltaDataδ
    (by
      intro cn iid cidx ar hc har
      by_cases h : cn = `c
      · subst h
        rw [ΓFOd_ctorsC] at hc; rw [ΓFOd_ctorAritiesC] at har
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        rw [show constructorArity Eδ ⟨toKername `I, 0⟩ 0 = some 0 by decide]; exact har
      · simp [ΓFOd, if_neg h] at hc)
    (by
      intro cn iid cidx hc
      by_cases h : cn = `c
      · subst h; rfl
      · simp [ΓFOd, if_neg h] at hc)
    (recEnvConsistent_of_noRec (Γ := ΓFOd) rfl) rfl H HD C Hδ hrun
    (gBridgeInv_nil envδ [] knownδ ΓFOd (fun _ => rfl) rfl (gw w) cfg (by simp [ΓFOd]))
    (.const `g [] (Or.inl rfl) (by simp [ΓFOd]) rfl)
    envδ_trG hnb gSEvalδ (envδ_foC_d harity)

/-- **The cold-start capstone at a non-empty fragment.** The same statement the two
guards above instantiate at `known = ⊥`, here at `knownδ`/`Esrcδ`: what it shows is that
δ-inclusion reaches the *entry point* — nothing in the cold-start composition forces the
empty fragment any more, and `SEnvConsistent` arrives constructed rather than vacuous.

The prepared subject stays hypothetical, and unavoidably so: `Erasure.erase` erases
`prepare_erasure e`, which no in-logic term can name (see the section docstring). -/
example (harity : ¬ IsArityUpTo envδ 0 [] (.const `I []))
    (cfg : ErasureConfig) (hcsimp : cfg.csimp = false)
    (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps envδ [] ΓFOd gw) (HD : DataBridgeHyps ΓFOd gw)
    (C : CasesBridgeHyps ΓFOd gw) (Hr : RegBridgeHyps ΓFOd)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps envδ [] knownδ ΓFOd Esrcδ gw cc rf)
    {e : Expr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {p : Program} {inls : List Kername}
    (S : ColdStartSubject envδ [] knownδ ΓFOd e cfg cctx ref w)
    (hev : ∀ {pe : Expr} {sp sf : ErasureState} {wp wt : Void IO.RealWorld} {t : LBTerm},
      Erasure.prepare_erasure e {} { «config» := cfg } cctx ref w = .ok (pe, sp) wp →
      Erasure.visitExpr pe sp { «config» := cfg } cctx ref wp = .ok (t, sf) wt →
      SEvalDataC ΓFOd (Esrcδ.walked ΓFOd sf.gdecls) pe (.const `c []))
    (hrun : Erasure.erase e cfg cctx ref w = .ok (p, inls) w') :
    ∃ (E : GlobalDeclarations) (t t' : LBTerm),
      p = .untyped E (some t) ∧
      WcbvEval E appliedFlags t t' ∧
      (∃ vve, TrExprS envδ [] [] (.const `c []) vve) ∧
      Erases envδ [] ΓFOd [] (.const `c []) t' ∧ NoBlock t' ∧
      ∀ tu, Erases envδ [] ΓFOd [] (.const `c []) tu → NoBlock tu → tu = t' :=
  shipping_erase_correct_firstorder_coldstart envδ_wf rfl hcsimp rfl rfl
    (by simp [ΓFOd]) Hr envδ_senvConsistent
    (by
      intro cn iid cidx hc
      by_cases h : cn = `c
      · subst h; rfl
      · simp [ΓFOd, if_neg h] at hc)
    H HD C Hδ S hev (envδ_foC_d harity) hrun

end DeltaGuard

end LeanToLambdaBox
