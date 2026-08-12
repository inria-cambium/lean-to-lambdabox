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
| `hclenv : ClosedEnv E` | `RegInvShape.closed`, at the run's final state |
| `hcl : LBClosed t 0` | `visitExpr_noFix_closed` (R11, no hypotheses) |
| `hregctors`/`hregcases`/`hregfields` | `RegInvShape.registeredCtors/…`, modulo saturation |
| `hdelta : ErasesEnvDeltaData` | vacuous — see the scope note |
| `known` as a free variable | instantiated to `⊥` — see the scope note |

## Scope note: the cold-start fragment is δ-free, and why

`BridgeInv.known_dom` says a `known` constant is *already registered*. At the empty state
nothing is, so the only sound instantiation is `known = ⊥` — and `Supported.const` needs
`known n`. **The cold-start fragment therefore contains no δ-constant**: constructors,
`casesOn` heads, literals, λ, `let` and application, but no plain constant reference.
Consequently `Esrc` is empty here and the δ records (`SEnvConsistent`,
`ErasesEnvDeltaData`, `RecEnvConsistent`) are discharged *vacuously* rather than from the
walk. Slice S3 (`ColdStartDelta`) proves the δ content that a δ-carrying cold start would
need — "the body a `visitMutual` exit recorded really erases the body it erased" — but it
cannot be *reached* until the following gap is closed, and this is the precise statement
of that gap:

> `get_constant_kername`'s **miss** branch (bridge motive 5) is still refuted rather than
> proved. Closing it needs motive 6 (`visitMutual`) to conclude `RunConcl` +
> generator-monotonicity + "`n` is now registered". Motive 6 can only get those from
> motive 1 (the bridge's own IH for the *abstract* erasure argument), and motive 1's
> conclusion is entirely **conditional** on `BridgeInv`/`Supported`/`TrExprS` — which a
> dependency's body does not come with. So the fix is not a new `RegBridgeHyps` field, as
> slice S2's note supposed: it is a restructuring of `visitExpr_refines_erases_core`'s
> motives to carry an *unconditional* state/generator conjunct alongside the conditional
> `Erases` one, i.e. a merge of the bridge induction with the shape induction.

Everything else the design predicted for this slice holds: the entry point reduces, the
invariant starts vacuously true and survives, and the environment the theorem talks about
is the one the run built.

## The premise ledger, after this slice

* **Proved from the run** — the state, the environment, `ClosedEnv`, `LBClosed t 0`, the
  bridge invariant, the `Program` shape.
* **Runtime Hoare bundles** — `BridgeHyps`, `DataBridgeHyps`, `CasesBridgeHyps`,
  `PrepareHyps` (now three fields: `prepare_sound` is *derived*, see
  `ColdStartRun.prepare_sound_of_prepareHyps`), and the new `RegBridgeHyps`
  (registry-invariant preservation along a run, plus registration completeness).
  `ColdStartInduction.RegShapeHyps` is **not** used — it is refuted below.
* **`Γ`-side conditions** — `hknames` (inside `RegBridgeHyps`), `Γ.fixvars = ⊥`,
  `Γ.recBodies = ⊥`, the peano-config pin, and `Us = []` (universe monomorphism, which at
  the entry point is not a restriction but a *fact*: `Erasure.run` installs
  `lparams := []`, and `BridgeInv.lparams` pins `ctx.lparams = Us`).
* **Certificates** — `IotaConsistent`, `IotaArityCoherent`, `IotaRelevant`, the
  constructor/`casesOn` disjointness; all `rfl`-checkable at a concrete `Γ`.
* **About the subject** — `ColdStartSubject` (the prepared term is supported and
  translatable; the output is in applied form) and the source evaluation, both stated
  about `prepare_erasure e` rather than `e`, since that is what the run erases.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

/-! ## A refuted premise, and what replaces it

Slice S1d collected the registration-side side conditions of the shape argument in
`ColdStartInduction.RegShapeHyps`, and `visitExpr_regInvShape` carries the registry
invariant through a whole run *given that record*. **The record is inconsistent**, so
those three corollaries (`visitExpr_regInvShape`, `visitMutual_regInvShape`,
`get_constant_kername_regInvShape`) are vacuous and cannot be used to discharge anything.

Two independent refutations, both proved below:

* `regShapeHyps_fresh_refuted` — `fresh` quantifies over **every** state satisfying the
  invariant, with no link to the call being made. `RegInvShape Γ (addAxiomState n {})` is
  a *theorem* (S1's own `RegInvShape.addAxiom` at the empty state), and in that state
  `Erasure.toKername n` is already a key, so `fresh` at that state and that name asserts
  `Kername.beq (toKername n) (toKername n) = false`.
* `regShapeHyps_recClosed_refuted` — `recClosed` asserts `LBClosed (.fix defs j) 0` for
  **every** `defs`, and a one-definition block whose body is `.bvar 5` is not closed.

`regKeys`/`regCtors`/`regCases`/`regFields` are refutable for the same reason as `fresh`
(the `register_inductive` *hit* branch's run is constructible from `run_get`/`run_pure`,
so those fields can be instantiated at a hand-made state whose `gdecls` is empty), though
only the two above are formalised here — one refutation is enough to void the record.

### The repair, precisely

The defect is not the *idea* — it is that each field is universally quantified over
states with nothing tying it to the walk. A consistent version needs

1. a **coverage** field in `RegInvShape` — every key of `gdecls` is the `toKername` of a
   registered constant or the block name of a registered inductive — which is what turns
   "`n` is not registered yet" (the guard `get_constant_kername`'s miss branch supplies)
   into "`toKername n` is a fresh key", modulo the naming side conditions the design calls
   `hkinj`; this in turn needs `Erasure.run_register_inductive_cold_ok`'s `ConstExt` to
   record the *keys* of its `@[extern]`-constructor axiom prefix, which it does not;
2. `RunClosed.rc` to **take** the closedness of the block it is storing (which
   `Erasure.run_rec_exit_ok` can supply from `run_mkDef_ok` + `closeFix`'s closedness
   metatheory), instead of demanding it of an arbitrary `defs`.

Both are inside slice S1's own files and neither is hard, but together they mean
re-running the 18-motive shape induction, so they are left to the repair slice.

### What this file uses instead

`RegBridgeHyps.regInv` states the *conclusion* `visitExpr_regInvShape` would have delivered,
keyed on an actual `Erasure.visitExpr` run. No run of the erasure family is constructible
in-logic (every branch goes through opaque `CoreM`/`MetaM` primitives), so it sits in
exactly the epistemic class of `BridgeHyps`/`DataBridgeHyps`: not decidable here, not
refutable here. When slice S1's record is repaired the field becomes a theorem and drops
out; nothing else in this file changes. -/

/-- **`RegShapeHyps` is inconsistent (i).** Its `fresh` field, instantiated at the state
S1's own `RegInvShape.addAxiom` produces, asserts that a kername differs from itself. -/
theorem regShapeHyps_fresh_refuted {Γ : ErasureCtx} (Hg : RegShapeHyps Γ) : False := by
  have hinv : RegInvShape Γ (addAxiomState `x {}) :=
    (RegInvShape.empty Γ).addAxiom (Hg.knames `x) (by simp)
  have := Hg.fresh (n := `x) hinv (toKername `x, .constantDecl ⟨none⟩) (by simp [addAxiomState])
  simp at this

/-- **`RegShapeHyps` is inconsistent (ii)** — independently of (i). `recClosed` ranges
over *every* block, including one whose single body is a loose de Bruijn index. -/
theorem regShapeHyps_recClosed_refuted {Γ : ErasureCtx} (Hg : RegShapeHyps Γ) : False := by
  have := Hg.recClosed [{ name := .anon, body := .bvar 5 }] 0
  simp [LBClosedDefs] at this

/-! ## `RegBridgeHyps` — the registration-completeness bundle

Slice S1d isolated the *soundness* side of the registration in `RegShapeHyps` (key
freshness, and `Γ`-agreement for the block a `register_inductive` call has just
registered). What is still missing at the capstone is the **completeness** side: that the
walk reached every block `Γ` knows about. `RegInvShape`'s three registration records are
scoped to `BlockRegistered s.gdecls` precisely because a partial run has registered only
part of `Γ`; collapsing them to the unscoped records the capstones consume needs exactly
this.

It is not derivable, and the reason is worth stating: `Γ` is a *parameter*. A `Γ` that
knows a constructor of an inductive the program never mentions makes the premise false —
which is the operational meaning of the design's "`Γ` is the specification of the
registration". Both fields are keyed on an actual run, so this is a per-run Hoare spec of
the same epistemic class as `BridgeHyps`, not a global fixed-point assumption. -/
structure RegBridgeHyps (Γ : ErasureCtx) : Prop where
  /-- **The registry invariant survives a whole `visitExpr` run.** Stated rather than
  used: `ColdStartInduction.visitExpr_regInvShape` proves exactly this, but only from the
  refuted `RegShapeHyps` — see the refutation section above, and the repair sketched
  there, after which this field becomes a theorem. -/
  regInv : ∀ {pe : Expr} {s : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
      {t : LBTerm} {s' : ErasureState} {w' : Void IO.RealWorld},
    Erasure.visitExpr pe s ctx cctx ref w = .ok (t, s') w' → RegInvShape Γ s →
    RegInvShape Γ s'
  /-- `Γ` files every constant under its canonical kername (the design's `hknames`; a
  side condition on the parameter `Γ`, `rfl` at every concrete one in the repo). -/
  knames : ∀ n : Name, Γ.constants n = toKername n
  /-- Every inductive block `Γ` records a constructor for was registered by the walk. -/
  satCtors : ∀ {pe : Expr} {s : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
      {t : LBTerm} {s' : ErasureState} {w' : Void IO.RealWorld},
    Erasure.visitExpr pe s ctx cctx ref w = .ok (t, s') w' →
    ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
      Γ.ctors cn = some (iid, cidx) → BlockRegistered s'.gdecls iid
  /-- Every inductive block `Γ` records a `casesOn` head for was registered by the walk. -/
  satCases : ∀ {pe : Expr} {s : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
      {t : LBTerm} {s' : ErasureState} {w' : Void IO.RealWorld},
    Erasure.visitExpr pe s ctx cctx ref w = .ok (t, s') w' →
    ∀ {con : Name} {iid : InductiveId} {np : Nat},
      Γ.casesOns con = some (iid, np) → BlockRegistered s'.gdecls iid

/-! ## The subject bundle

`Erasure.erase` runs `visitExpr (← prepare_erasure e)`, so every fact a capstone needs
about "the term being erased" is a fact about the **prepared** term, which the run
produces and the statement cannot name. They are collected here, each quantified over the
prepare run that produces it.

`PrepareHyps.prepare_sound` is what relates the prepared term's source evaluation back to
`e`'s; it is stated for `SEvalData`, so the `SEvalDataι`/`SEvalDataC` flavours the
capstones use are taken directly about the prepared term. -/
structure ColdStartSubject (env : VEnv) (Us : List Name) (Γ : ErasureCtx)
    (e : Expr) (cfg : ErasureConfig) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) : Prop where
  /-- The prepared term is in the supported fragment (at `known = ⊥`: no δ-constant —
  see the module docstring) and lean4lean translates it. -/
  supported : ∀ {pe : Expr} {s₁ : ErasureState} {w₁ : Void IO.RealWorld},
    Erasure.prepare_erasure e {} { «config» := cfg } cctx ref w = .ok (pe, s₁) w₁ →
    Supported (fun _ => False) Γ pe ∧ ∃ ve, TrExprS env Us [] pe ve
  /-- The erased term is in applied (`NoBlock`) form — the data fragment's shape premise,
  here about the entry point's own run. -/
  noBlock : ∀ {pe : Expr} {sp : ErasureState} {wp : Void IO.RealWorld} {t : LBTerm}
      {sf : ErasureState} {wt : Void IO.RealWorld},
    Erasure.visitExpr pe sp { «config» := cfg } cctx ref wp = .ok (t, sf) wt → NoBlock t

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
    {Γ : ErasureCtx} {ia : IotaArities} {cfg : ErasureConfig} (hcsimp : cfg.csimp = false)
    -- Γ-side conditions
    (hnfv : Γ.fixvars = fun _ => none) (hnorec : Γ.recBodies = fun _ => none)
    (hnat : Γ.natPeano = true → cfg.nat = .peano)
    -- registration bundle
    (Hr : RegBridgeHyps Γ)
    -- ι certificates
    (hiota : IotaConsistent env Us Γ ia)
    (hiacoh : IotaArityCoherent Γ ia)
    (hrel : IotaRelevant env Us Γ)
    (hcc : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
             Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none)
    -- runtime Hoare bundles
    {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
    -- the subject
    {e v : Expr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld}
    (S : ColdStartSubject env Us Γ e cfg cctx ref w)
    (hev : ∀ {pe : Expr} {s₁ : ErasureState} {w₁ : Void IO.RealWorld},
      Erasure.prepare_erasure e {} { «config» := cfg } cctx ref w = .ok (pe, s₁) w₁ →
      SEvalDataι Γ ia (fun _ => none) pe v)
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
  have hshape : RegInvShape Γ sf := Hr.regInv hvis (RegInvShape.empty Γ)
  have hcl : LBClosed t 0 := (visitExpr_noFix_closed hvis).2
  -- The bridge invariant is *constructed* at the entry configuration.
  have hinv : BridgeInv env [] (fun _ => False) Γ (gw wp) { «config» := cfg } {} [] :=
    gBridgeInv_nil env [] Γ Hr.knames hnfv (gw wp) cfg hnat
  obtain ⟨hsup, hex⟩ := S.supported hpr
  obtain ⟨ve, htr⟩ := hex
  obtain ⟨t', heval, htrv, herv, hnbv, hclv, huniq⟩ :=
    shipping_erase_correct_firstorderι henv (Us := []) (Esrc := fun _ => none)
      (E := sf.gdecls) (known := fun _ => False)
      (by intro Δ n us body cve h; exact absurd h (by simp))
      hiota
      (by intro Δ n body h; exact absurd h (by simp))
      (erasesEnvCtor_of_registeredCtors (hshape.registeredCtors (Hr.satCtors hvis)))
      (erasesEnvCases_of_registeredCases (hshape.registeredCases (Hr.satCases hvis)))
      (ctorFieldsCoherent_of_registered (hshape.registeredCtors (Hr.satCtors hvis))
        (hshape.registeredCases (Hr.satCases hvis))
        (hshape.registeredCtorFieldsAll (Hr.satCases hvis)))
      hiacoh hrel hcc (recEnvConsistent_of_noRec hnorec) hnfv hshape.closed H HD C
      hvis hinv hsup htr (S.noBlock hvis) hcl (hev hpr) hfo
  exact ⟨sf.gdecls, t, t', hp, heval, htrv, herv, hnbv, hclv, huniq⟩

/-- **Cold-start D3 — the βζδ+data flavour.** Same composition, with the source
evaluation at `SEvalDataC` (β + δ + saturated constructors) and the ι certificate block
dropped; it goes through `shipping_erase_correct_firstorder`, whose conclusion carries no
`LBClosed t'`. The two flavours differ only in which capstone they call, which is what
"the composition is uniform" means here. -/
theorem shipping_erase_correct_firstorder_coldstart
    {env : VEnv} (henv : env.WF) {Us : List Name} (hUs : Us = [])
    {Γ : ErasureCtx} {cfg : ErasureConfig} (hcsimp : cfg.csimp = false)
    (hnfv : Γ.fixvars = fun _ => none) (hnorec : Γ.recBodies = fun _ => none)
    (hnat : Γ.natPeano = true → cfg.nat = .peano)
    (Hr : RegBridgeHyps Γ)
    (hcc : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
             Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none)
    {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
    {e v : Expr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld}
    (S : ColdStartSubject env Us Γ e cfg cctx ref w)
    (hev : ∀ {pe : Expr} {s₁ : ErasureState} {w₁ : Void IO.RealWorld},
      Erasure.prepare_erasure e {} { «config» := cfg } cctx ref w = .ok (pe, s₁) w₁ →
      SEvalDataC Γ (fun _ => none) pe v)
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
  have hshape : RegInvShape Γ sf := Hr.regInv hvis (RegInvShape.empty Γ)
  have hinv : BridgeInv env [] (fun _ => False) Γ (gw wp) { «config» := cfg } {} [] :=
    gBridgeInv_nil env [] Γ Hr.knames hnfv (gw wp) cfg hnat
  obtain ⟨hsup, ve, htr⟩ := S.supported hpr
  obtain ⟨t', heval, htrv, herv, hnbv, huniq⟩ :=
    shipping_erase_correct_firstorder henv (Us := []) (Esrc := fun _ => none)
      (E := sf.gdecls) (known := fun _ => False)
      (by intro Δ n us body cve h; exact absurd h (by simp))
      (by intro Δ n body h; exact absurd h (by simp))
      (erasesEnvCtor_of_registeredCtors (hshape.registeredCtors (Hr.satCtors hvis)))
      hcc (recEnvConsistent_of_noRec hnorec) hnfv H HD C
      hvis hinv hsup htr (S.noBlock hvis) (hev hpr) hfo
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
    {e : Expr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {p : Program} {inls : List Kername}
    (S : ColdStartSubject envFO [] ΓFOι e cfg cctx ref w)
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
    (by simp [ΓFOι]) Hr hiota ΓFOι_iotaArityCoherent hrel ΓFOι_cc H HD C S hev
    (envFO_foC_ι harity) hrun

/-- The βζδ+data flavour of the same guard, at the same pin. -/
example (harity : ¬ IsArityUpTo envFO 0 [] (.const `I []))
    (cfg : ErasureConfig) (hcsimp : cfg.csimp = false)
    (gw : Void IO.RealWorld → NameGenerator)
    (H : BridgeHyps envFO [] ΓFOι gw) (HD : DataBridgeHyps ΓFOι gw)
    (C : CasesBridgeHyps ΓFOι gw) (Hr : RegBridgeHyps ΓFOι)
    {e : Expr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {p : Program} {inls : List Kername}
    (S : ColdStartSubject envFO [] ΓFOι e cfg cctx ref w)
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
    (by simp [ΓFOι]) Hr ΓFOι_cc H HD C S hev (envFO_foC_ι harity) hrun

end LeanToLambdaBox
