import LeanToLambdaBox.Bridge
import LeanToLambdaBox.ErasureRun
import LeanToLambdaBox.SourceEval
import Lean4Lean.Verify.NameGenerator

/-!
# The δ-closure bundle: `DeltaHyps`

This structure sits *beside* `BridgeHyps` (`VisitExprRefines.lean`), `DataBridgeHyps`
(`DataBridgeHyps.lean`) and `CasesBridgeHyps` (`CasesBridgeHyps.lean`), and carries what it
costs to let an erased program **call** something — the δ (constant-unfolding) fragment.

## Why a bundle and not an invariant field

`BridgeInv` (`VisitExprRefines.lean`) is the *state-side* half of the bridge's contract: it
relates the reader and the registry to `Γ` at the entry state of each sub-run. A cold start
begins at the empty state, so no *state* condition can say anything about a constant the
walk has not reached yet — that is exactly the wall `BridgeInv.known_dom` ran into, and
recording a δ-obligation there would make it unsatisfiable at `{}` rather than merely
strong. What a δ-reference actually needs is the *scope-side* half: the fragment `known` is
closed under dependency, each dependency's prepared body is itself in the fragment, and the
declaration fetch agrees with `Esrc`. None of that mentions a state, so all of it lives
here, Hoare-shaped, one clause per real runtime call.

## Epistemic class

`BridgeHyps` (`VisitExprRefines`) and `RegBridgeHyps` (`ColdStartInduction`): every field is
either a Hoare spec for one *real* call on the `visitMutual` registration path — never an
axiom, never a statement about an entire environment — or a scope statement about the
fragment `known`. All the primitives specced here (`Compiler.LCNF.getDeclInfo?`, `getEnv`,
`logInfo`, `Meta.isInstance`, `getConstInfo`, `prepare_erasure`, `addAxiom`) are **real**:
none of them belongs to the `visitExpr` mutual block, so their specs are usable directly
inside `Erasure.visitExpr.mutual_fixpoint_induct`. Because they quantify over opaque
runtime primitives their global satisfiability is not in-logic decidable — the documented
trust boundary, exactly as for `BridgeHyps`/`DataBridgeHyps`/`CasesBridgeHyps`.

`mkFreshFVarId` is deliberately **absent**: `BridgeHyps.fresh_run` already specs it, and the
recursive exit's block ids are the only place the registration path mints one.

## The four scope restrictions this bundle makes operational

They were latent in the development before; here each is a field, so a `Γ`/`known` that
violates one makes the bundle *unsatisfiable* — the right failure mode, but only because it
is written down:

1. **Universe monomorphism of the whole dependency cone.** `Erases` is indexed by a single
   `Us`, while `visitMutual` erases a dependency's body under
   `withReader (… lparams := ci.levelParams)`. `decl_run` therefore demands
   `ci.levelParams = Us`: realistically `Us = []` and every dependency monomorphic. A
   polymorphic dependency does not make any theorem *false*; it makes `DeltaHyps`
   uninhabited.
2. **Non-recursive dependencies.** `Erasure.ErasureContext.fixvars` is installed per block
   while `Γ.fixvars` is a single global map, so one `Γ` cannot be both "outside every block"
   (what a top-level subject needs) and "inside this block" (what a recursive dependency's
   body needs). `nofixvars` pins the first; lifting the restriction means moving `Γ` inside
   the bridge's motives, which is a separate, larger change.
3. **No fragment constant is emitted as an axiom.** `axiom_free` covers both `addAxiom`
   sites — the value-less and `@[extern] + preferAxiom` exits of `visitMutual` — which is
   what a capstone needs to know that a fragment constant the walk reached really has a
   recorded *body* and not a value-less axiom entry.
4. **Fragment names are distinguished by their kernames.** `Erasure.toKername` is not
   injective, so without `kinj` the δ *record* below is false whenever two fragment names
   collide on a key. It is the fragment-scoped form of the capstone's `hkinj`.

## Two environments, deliberately: the fragment and the evaluation's

`Esrc` here is a **scope** — the collection of prepared bodies the erased program is
allowed to call — and the `prep_esrc` clause pins the *walk*'s declaration fetches
against it. The forward simulations take an `Esrc` too, but theirs is
the environment the *source evaluation* δ-unfolds, and at a cold start that one is
necessarily smaller: the walk registers only what the program reached
(`ColdStartDelta.SEnv.walked`). Every theorem downstream of the bridge therefore carries
the two separately — the bundle at `Esrcδ`, the simulation at its own `Esrc` — because
conflating them forces either a *false* record (the unrestricted `ErasesEnvDeltaData`,
which claims registrations for constants the walk never reached) or a bundle at the
restricted environment, which `prep_esrc` cannot satisfy: it fixes `Esrc` at the moment
the walk prepares a body, before there is a final state to restrict against. No theorem
relates the two; a caller that wants them equal simply passes one environment twice.

## The record, and the one residue that is not a scope statement

`DeltaMem` and `RunConclδ` (below) are not hypotheses at all: they are what the bridge
*proves* about a run, and they live here because the bridge's motives mention them.

`uniform` is the `∀ Δ` context-uniformity residue that
`ColdStartDelta.registeredClosureData_step_nonrec` already carries as `huni`: the bridge
fires at the `Δ = []` the run uses, while a δ-unfolding happens at an arbitrary `Δ`.
`Erases` has `abstract`/`uninstantiate`/`thin_vlet`, all context-*shrinking*; the missing
direction is fvar-extension of `Δ`, which is a lean4lean-side `TrExprS` weakening
obligation, not an erasure one. It is a premise here for exactly as long as that lemma is
missing.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

/-- **The δ-closure bundle.** What it costs to let the erased term *call* something.

`known` is the fragment: the constants the erased program may reference. `Esrc` is the
source environment the *evaluation* δ-unfolds; `esrc_sub` says it is a sub-collection of
the fragment (an axiom-emitted constant may be `known` but has no `Esrc` entry, and a
program that forces one does not evaluate).

The five `…_run` bookkeeping clauses are the generator-monotonicity specs for the
primitives only `visitMutual` reaches; `BridgeHyps` covers the four the *term* path
touches, and this bundle deliberately does not duplicate them.

Two clauses are keyed on a *pair* of runs rather than one: `prep_esrc` (the declaration
fetch plus the preparation of its value) and, at the consumer, `prepared`. That shape is
forced by the point of use — inside `Erasure.visitExpr.mutual_fixpoint_induct` the caller
holds runs, not an environment — and is documented at each field. -/
structure DeltaHyps (env : VEnv) (Us : List Name) (known : Name → Prop) (Γ : ErasureCtx)
    (Esrc : SEnv) (gw : Void IO.RealWorld → NameGenerator)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State) : Prop where
  /-- `Esrc`'s domain is inside the fragment. -/
  esrc_sub : ∀ {n : Name}, (Esrc n).isSome → known n
  /-- Fragment constants are plain constants — neither a registered constructor nor a
  registered `casesOn` head. (The same conjunct `RegisteredClosureData.disj` carries, and
  what kills the constructor-spine disjunct of `Erases.app_inv` in a δ case.) -/
  disj : ∀ {n : Name}, known n → Γ.ctors n = none ∧ Γ.casesOns n = none
  /-- **Fragment names are distinguished by their kernames** — scope restriction 4, and
  the one the δ *record* needs rather than the δ *reference* (slice D4b).

  `Erasure.toKername` is **not** injective (`ColdStartShape.mutualBlockKn_eq_toKername`:
  the block-key and constant-key spaces genuinely overlap), so two distinct names can be
  filed in `gdecls` under one key. A record saying "the body stored under `Γ.constants n`
  erases what `Esrc` records for `n`" is then simply false for one of them, and the walk
  cannot repair it — it stores one entry per registration and never looks at the other
  name. Restricting the claim to the fragment is what makes it true, and it is the
  fragment-scoped form of the `hkinj` naming-scheme assumption the cold-start capstone has
  to pay anyway for `KeysDistinct`. -/
  kinj : ∀ {m m' : Name}, known m → known m' → Γ.constants m = Γ.constants m' → m = m'
  /-- **No block-local fixvar map** — scope restriction 2. This is the `hnfv` every
  top-level capstone already pins, moved into the bundle because it is exactly what the
  dependency's reader (`withReader (… fixvars := .none …)`) has to agree with. -/
  nofixvars : Γ.fixvars = fun _ => none
  /-- **The declaration fetch agrees with the fragment.** For a `known` name: the fetch is
  generator-monotone, the block is a *single* declaration, it is universe-monomorphic at
  the ambient `Us` (scope restriction 1), and — when it has a value — that value does not
  mention the constant itself (so `visitMutual`'s `nonrecursive` test is forced `true`, and
  the recursive exit is out of scope).

  It used to carry a fourth conjunct, `(Esrc n).isSome`. Slice D4a made it dead: naming
  *some* body is never enough at the point of use, which needs *this* run's body, and
  `prep_esrc` states that identification directly. Dropping it weakens the bundle, so
  every consumer is unaffected.

  Stated at the `CoreM` layer, which is the layer `ColdStartRun.run_visitMutual_decomp`
  hands the fetch back at. -/
  decl_run : ∀ {n : Name} {w w₁ : Void IO.RealWorld} {r : Option ConstantInfo},
    known n →
    (Compiler.LCNF.getDeclInfo? n : CoreM (Option ConstantInfo)) cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧ ∃ ci, r = some ci ∧ ci.all = [n] ∧ ci.levelParams = Us ∧
      (∀ v, ci.value? (allowOpaque := true) = some v → name_occurs n v = false)
  /-- **The prepared dependency body is in the fragment.** Quantified over the
  `prepare_erasure` run that produces it, exactly as `ColdStartSubject.supported` is for the
  top-level subject: this is the *same* premise, generalised from "the subject" to "the
  subject and every constant it calls", and it should be read in one breath with that one
  rather than as a second, independent restriction. The `Supported` half is a genuine
  fragment restriction (no `.proj`, no η-contracted minors, no machine `Nat`); the `∀ Δ` on
  the translatability is there only because `TrExprS` weakening is missing — see `uniform`.

  Note for the consumer: `Esrc n = some pe` is a *premise*, at the run's own output `pe`.
  That is the canonical instantiation's defining equation (`Esrc` **is** the collection of
  prepared bodies), not something to be derived from the run — `prep_esrc` below is what
  hands it to a caller who has only the run. -/
  prepared : ∀ {n : Name} {v pe : Expr} {s s₁ : ErasureState} {ctx : ErasureContext}
      {w w₁ : Void IO.RealWorld},
    known n → Esrc n = some pe →
    prepare_erasure v s ctx cctx ref w = .ok (pe, s₁) w₁ →
    Supported known Γ pe ∧ (∀ Δ : VLCtx, ∃ ve, TrExprS env Us Δ pe ve)
  /-- **`Esrc` records the prepared body of the declaration the walk fetched** — the
  run-keyed half of `prepared`'s premise, and the canonical instantiation's defining
  equation (slice D4a).

  `prepared` is keyed on `Esrc n = some pe` at the run's *own* output `pe`. A caller
  inside the bridge induction holds the `prepare_erasure` run and `decl_run`'s
  `(Esrc n).isSome`, and those two cannot be joined: `(Esrc n).isSome` names *some* body,
  the run produces *its* body, and nothing in the logic identifies the two. So the
  identification is stated here, keyed on exactly the two runs such a caller has in hand —
  the `getDeclInfo?` fetch, which is what ties the value `v` to the name `n` (without it
  the clause would be plainly false: `prepare_erasure` runs on every expression the walk
  prepares, the top-level subject included), and the `prepare_erasure` run itself.

  It is the same fact `ColdStartDelta.registeredClosureData_step_nonrec` takes as its
  `hEsrc` premise at the composition site; it lives in the bundle because inside the
  induction there is no composition site to take it at. -/
  prep_esrc : ∀ {n : Name} {ci : ConstantInfo} {r : Option ConstantInfo} {v pe : Expr}
      {s s₁ : ErasureState} {ctx : ErasureContext}
      {wd wd₁ w w₁ : Void IO.RealWorld},
    known n →
    (Compiler.LCNF.getDeclInfo? n : CoreM (Option ConstantInfo)) cctx ref wd = .ok r wd₁ →
    r = some ci → ci.value? (allowOpaque := true) = some v →
    prepare_erasure v s ctx cctx ref w = .ok (pe, s₁) w₁ →
    Esrc n = some pe
  /-- **No fragment constant is emitted as an axiom** — scope restriction 3. Covers both
  `addAxiom` sites: `visitMutual`'s value-less / `@[extern] + preferAxiom` exits, and the
  `@[extern]`-constructor prefix inside `register_inductive`. -/
  axiom_free : ∀ {m : Name} {s s' : ErasureState} {ctx : ErasureContext}
      {w w' : Void IO.RealWorld} {u : Unit},
    addAxiom m s ctx cctx ref w = .ok (u, s') w' → Esrc m = none
  /-- Bookkeeping: `logInfo` is generator-monotone. -/
  log_run : ∀ {m : MessageData} {u : Unit} {s s' : ErasureState} {ctx : ErasureContext}
      {w w' : Void IO.RealWorld},
    (logInfo m : EraseM Unit) s ctx cctx ref w = .ok (u, s') w' → gw w ≤ gw w'
  /-- Bookkeeping: `getEnv` is generator-monotone. -/
  env_run : ∀ {e : Environment} {s s' : ErasureState} {ctx : ErasureContext}
      {w w' : Void IO.RealWorld},
    (getEnv : EraseM Environment) s ctx cctx ref w = .ok (e, s') w' → gw w ≤ gw w'
  /-- Bookkeeping: the typeclass-instance test is generator-monotone. -/
  inst_run : ∀ {m : Name} {b : Bool} {s s' : ErasureState} {ctx : ErasureContext}
      {w w' : Void IO.RealWorld},
    (liftM (Lean.Meta.isInstance m) : EraseM Bool) s ctx cctx ref w = .ok (b, s') w' →
      gw w ≤ gw w'
  /-- Bookkeeping: `getConstInfo` is generator-monotone. (Its *state* transparency is
  proved, `Erasure.run_getConstInfo_state`, and is not assumed here.) -/
  ci_run : ∀ {m : Name} {ci : ConstantInfo} {s s' : ErasureState} {ctx : ErasureContext}
      {w w' : Void IO.RealWorld},
    (getConstInfo m : EraseM ConstantInfo) s ctx cctx ref w = .ok (ci, s') w' → gw w ≤ gw w'
  /-- Bookkeeping: `prepare_erasure` is generator-monotone and leaves the `ErasureState`
  alone.

  The state conjunct is the `hprep`-class item `ErasureRun`'s registration-exit rules
  already carry (`Erasure.run_nonrec_exit_ok`'s `hprep`, whose docstring gives the same
  classification): `prepare_erasure`'s `csimp` branch runs `Lean.Core.transform` *at*
  `EraseM` through `MonadControlT`, so state transparency does not follow from the `liftM`
  lemmas the way it does for the other four primitives here. It is *proved* for every
  csimp-off configuration (`ColdStartRun.run_prepare_erasure_state`), and csimp-off is the
  only configuration any capstone runs in — `PrepareHyps`' gate, for the independent
  reason that csimp replacement is not kernel-semantics-preserving. It is assumed rather
  than derived here (slice D4a) because the reader's config is an *induction variable*
  inside the bridge: `BridgeInv` does not pin `csimp`, so the gate is not visible at the
  point of use. A csimp-on instance of this bundle is out of scope, which is the failure
  mode the gate already fixes everywhere else. -/
  prep_run : ∀ {e pe : Expr} {s s' : ErasureState} {ctx : ErasureContext}
      {w w' : Void IO.RealWorld},
    prepare_erasure e s ctx cctx ref w = .ok (pe, s') w' → gw w ≤ gw w' ∧ s' = s
  /-- **Context-uniformity of a constant body's erasure** — the `huni` residue
  `ColdStartDelta.registeredClosureData_step_nonrec` already carries. Discharged outright
  once `Erases`/`TrExprS` gain fvar-extension weakening; a premise until then.

  Stated between *two* arbitrary contexts rather than out of `Δ = []` (slice D5). The
  `[]`-shaped form is what a caller holding the run needs, because `visitMutual` erases a
  top-level constant body at the empty context; but the record the walk hands the capstone
  (`DeltaMem`) carries `∃ Δ` — the `Δ` of the *call site*, since `withReader` keeps the
  ambient `lctx` — and `RegisteredClosure*.erase` demands `∀ Δ`. Nothing weaker than the
  two-sided form bridges those, and the one-sided form is its instance at `Δ := []`. -/
  uniform : ∀ {n : Name} {pe : Expr} {t : LBTerm} {Δ Δ' : VLCtx},
    Esrc n = some pe → Erases env Us Γ Δ pe t → Erases env Us Γ Δ' pe t

/-- **What the bundle costs at the empty fragment** — the honest accounting for every
consumer that still runs at `known = ⊥` (all of them, until the capstone rewiring).

The *scope* half is free there and is discharged below: `esrc_sub`, `disj`, `decl_run`,
`prepared`, `prep_esrc` and `uniform` all have `known n` or `(Esrc n).isSome` in their
premises, and `axiom_free`'s conclusion is `none = none`. The *bookkeeping* half is
**not** free and is passed in: `log_run`/`env_run`/`inst_run`/`ci_run`/`prep_run` are
generator-monotonicity (and, for `prep_run`, state-transparency) statements about real
primitives, and `gw` is an arbitrary map from world tokens to generators — nothing in the
logic makes `gw w ≤ gw w'` hold across a world-advancing call. They are the same
epistemic class as `BridgeHyps.fresh_run`, which is why `BridgeHyps` assumes its four and
this bundle its five. `nofixvars` is likewise a real side condition on `Γ` — the `hnfv`
every top-level entry point already pins.

So: a `known = ⊥` consumer buys exactly six things, and no fragment-scope obligation. -/
theorem DeltaHyps.of_bot {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {gw : Void IO.RealWorld → NameGenerator} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State}
    (hnfv : Γ.fixvars = fun _ => none)
    (hlog : ∀ {m : MessageData} {u : Unit} {s s' : ErasureState} {ctx : ErasureContext}
        {w w' : Void IO.RealWorld},
      (logInfo m : EraseM Unit) s ctx cctx ref w = .ok (u, s') w' → gw w ≤ gw w')
    (henv : ∀ {e : Environment} {s s' : ErasureState} {ctx : ErasureContext}
        {w w' : Void IO.RealWorld},
      (getEnv : EraseM Environment) s ctx cctx ref w = .ok (e, s') w' → gw w ≤ gw w')
    (hinst : ∀ {m : Name} {b : Bool} {s s' : ErasureState} {ctx : ErasureContext}
        {w w' : Void IO.RealWorld},
      (liftM (Lean.Meta.isInstance m) : EraseM Bool) s ctx cctx ref w = .ok (b, s') w' →
        gw w ≤ gw w')
    (hci : ∀ {m : Name} {ci : ConstantInfo} {s s' : ErasureState} {ctx : ErasureContext}
        {w w' : Void IO.RealWorld},
      (getConstInfo m : EraseM ConstantInfo) s ctx cctx ref w = .ok (ci, s') w' →
        gw w ≤ gw w')
    (hprep : ∀ {e pe : Expr} {s s' : ErasureState} {ctx : ErasureContext}
        {w w' : Void IO.RealWorld},
      prepare_erasure e s ctx cctx ref w = .ok (pe, s') w' → gw w ≤ gw w' ∧ s' = s) :
    DeltaHyps env Us (fun _ => False) Γ (fun _ => none) gw cctx ref where
  esrc_sub := by intro n h; simp at h
  disj := fun h => h.elim
  kinj := fun h => h.elim
  nofixvars := hnfv
  decl_run := fun h => h.elim
  prepared := fun h => h.elim
  prep_esrc := fun h => h.elim
  axiom_free := fun _ => rfl
  log_run := hlog
  env_run := henv
  inst_run := hinst
  ci_run := hci
  prep_run := hprep
  uniform := by intro n pe t Δ Δ' h; simp at h

/-! ## The δ record along the walk

`DeltaHyps` is what a δ-*reference* costs. What follows is what a δ-*record* is: the fact
the walk produces about the bodies it registers, in the form that survives being carried
through the bridge induction. -/

/-- **The δ record, membership-flavoured.** Every constant body the walk has *recorded* for
a fragment name really erases the source body `Esrc` records for it.

Three deliberate choices, each forced by where this has to travel:

* **membership in `gdecls`, not `envLookup`.** `RegisteredClosureData.mono` needs
  `KeysDistinct` to transport, and slice S1e proved that no state predicate carried along
  the walk can maintain key distinctness (`ColdStartInduction.runClosed_keysDistinct_refuted`).
  Membership needs no key discipline; `ColdStartDelta.envLookup_of_mem_of_keys` converts
  once, at the end, where `KeysDistinct` is a capstone premise anyway.
* **keyed on the recorded entry, not on the registry domain.** The domain grows at
  *every* `addAxiom`, including the `@[extern]`-constructor prefix inside
  `register_inductive`, and killing those needs the `addAxiom` runs, which
  `Erasure.run_register_inductive_cold_ok` does not hand back (it exposes a `ConstExt`).
  Keyed on the entry, the same call transports for free: every entry it conses is either
  `.constantDecl ⟨none⟩` or an `.inductiveDecl`, and neither is of this shape. The
  existence half — "the walk did record a body for every fragment constant it reached" —
  is therefore *not* part of this record; it is a separate walk fact, and the capstone
  conversion below takes it as a premise.
* **`∃ Δ`, not `∀ Δ`.** The bridge fires at the `Δ` of the *call site*, and `visitMutual`'s
  `withReader` keeps the ambient `lctx`, so a dependency reached from inside a binder is
  erased at a non-empty `Δ`. Lifting to `∀ Δ` is the `uniform`/`huni` residue this
  development already carries as a premise everywhere else. -/
structure DeltaMem (env : VEnv) (Us : List Name) (Γ : ErasureCtx) (Esrc : SEnv)
    (s : ErasureState) : Prop where
  erase : ∀ {n : Name} {body : Expr} {t : LBTerm}, Esrc n = some body →
    (Γ.constants n, GlobalDecl.constantDecl ⟨some t⟩) ∈ s.gdecls →
    ∃ Δ : VLCtx, Erases env Us Γ Δ body t

/-- At the entry state there is nothing recorded, so the record holds. -/
theorem DeltaMem.empty {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Esrc : SEnv} :
    DeltaMem env Us Γ Esrc {} where
  erase := by intro n body t _ hm; simp at hm

/-- **The general transport.** A step that conses no `.constantDecl ⟨some _⟩` entry keeps
the record — that is every step of the walk except the two constant registrations. -/
theorem DeltaMem.mono_of_gdecls {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {Esrc : SEnv} {s s' : ErasureState} (h : DeltaMem env Us Γ Esrc s)
    (hg : ∀ {kn : Kername} {t : LBTerm},
      (kn, GlobalDecl.constantDecl ⟨some t⟩) ∈ s'.gdecls →
      (kn, GlobalDecl.constantDecl ⟨some t⟩) ∈ s.gdecls) :
    DeltaMem env Us Γ Esrc s' where
  erase := fun hb hm => h.erase hb (hg hm)

/-- Transport across a state whose `gdecls` did not move at all (the `@[inline]`
bookkeeping, and every state-transparent primitive). -/
theorem DeltaMem.of_gdecls_eq {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {Esrc : SEnv} {s s' : ErasureState} (h : DeltaMem env Us Γ Esrc s)
    (hg : s'.gdecls = s.gdecls) : DeltaMem env Us Γ Esrc s' :=
  h.mono_of_gdecls (by rw [hg]; exact id)

/-- Transport across an axiom registration: it conses a *value-less* entry, so it cannot
be the recorded body of anything. (This is why `DeltaHyps.axiom_free` is not needed to
carry the record — only to reach the capstone's existence half.) -/
theorem DeltaMem.addAxiom {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Esrc : SEnv}
    {s : ErasureState} (h : DeltaMem env Us Γ Esrc s) (m : Name) :
    DeltaMem env Us Γ Esrc (addAxiomState m s) := by
  refine h.mono_of_gdecls ?_
  intro kn t hm
  rcases List.mem_cons.mp hm with heq | hm'
  · exact absurd heq (by simp)
  · exact hm'

/-- **The one extension step.** The non-recursive exit conses the body it just erased; the
record grows by exactly that witness. -/
theorem DeltaMem.nonrec {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Esrc : SEnv}
    {s : ErasureState} {n : Name} {t : LBTerm} (h : DeltaMem env Us Γ Esrc s)
    (hkn : Γ.constants n = toKername n)
    (hinj : ∀ {m : Name}, (Esrc m).isSome → Γ.constants m = Γ.constants n → m = n)
    (hwit : ∀ {body : Expr}, Esrc n = some body → ∃ Δ : VLCtx, Erases env Us Γ Δ body t) :
    DeltaMem env Us Γ Esrc (nonrecConstState n t s) where
  erase := by
    intro m body t' hb hm
    rcases List.mem_cons.mp hm with heq | hm'
    · obtain ⟨hk, hd⟩ : Γ.constants m = toKername n ∧
          GlobalDecl.constantDecl ⟨some t'⟩ = GlobalDecl.constantDecl ⟨some t⟩ := by
        simpa using heq
      obtain rfl : t' = t := by simpa using hd
      obtain rfl : m = n := hinj (by rw [hb]; simp) (by rw [hk, hkn])
      exact hwit hb
    · exact h.erase hb hm'

/-- **The state-side conclusion every bridge motive carries** (slice D4b): the run grew the
state in the registration-only way `Erasure.RunConcl` describes, *and* it carried the δ
record with it. Bundling the two keeps the motives' shape — and the ~40 sites that produce
it — unchanged: a `RunConclδ` is produced and composed exactly where a `RunConcl` was. -/
structure RunConclδ (env : VEnv) (Us : List Name) (Γ : ErasureCtx) (Esrc : SEnv)
    (s s' : ErasureState) : Prop where
  rc : Erasure.RunConcl s s'
  δ : DeltaMem env Us Γ Esrc s → DeltaMem env Us Γ Esrc s'

theorem RunConclδ.rfl' {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Esrc : SEnv}
    (s : ErasureState) : RunConclδ env Us Γ Esrc s s :=
  ⟨Erasure.RunConcl.rfl' s, id⟩

theorem RunConclδ.of_eq {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Esrc : SEnv}
    {s s' : ErasureState} (h : s' = s) : RunConclδ env Us Γ Esrc s s' := by
  subst h; exact RunConclδ.rfl' _

theorem RunConclδ.trans {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Esrc : SEnv}
    {s s' s'' : ErasureState} (h : RunConclδ env Us Γ Esrc s s')
    (h' : RunConclδ env Us Γ Esrc s' s'') : RunConclδ env Us Γ Esrc s s'' :=
  ⟨h.rc.trans h'.rc, fun hm => h'.δ (h.δ hm)⟩

/-- The three registration deltas of `visitMutual`, as `RunConclδ` steps: the `@[inline]`
bookkeeping and the axiom exit record no body, and the non-recursive exit records exactly
the one the caller has just erased. -/
theorem RunConclδ.inlinings {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Esrc : SEnv}
    (s : ErasureState) (kn : Kername) :
    RunConclδ env Us Γ Esrc s { s with inlinings := kn :: s.inlinings } :=
  ⟨Erasure.runConcl_inlinings s kn, fun h => h.of_gdecls_eq rfl⟩

theorem RunConclδ.addAxiom {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Esrc : SEnv}
    (m : Name) (s : ErasureState) :
    RunConclδ env Us Γ Esrc s (Erasure.addAxiomState m s) :=
  ⟨Erasure.runConcl_addAxiomState m s, fun h => h.addAxiom m⟩

theorem RunConclδ.nonrec {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Esrc : SEnv}
    {s : ErasureState} {n : Name} {t : LBTerm}
    (hkn : Γ.constants n = toKername n)
    (hinj : ∀ {m : Name}, (Esrc m).isSome → Γ.constants m = Γ.constants n → m = n)
    (hwit : ∀ {body : Expr}, Esrc n = some body → ∃ Δ : VLCtx, Erases env Us Γ Δ body t) :
    RunConclδ env Us Γ Esrc s (Erasure.nonrecConstState n t s) :=
  ⟨Erasure.runConcl_nonrecConstState n t s, fun h => h.nonrec hkn hinj hwit⟩

/-- A step that conses no recorded body is a `RunConclδ` as soon as it is a `RunConcl`. -/
theorem RunConclδ.of_runConcl_gdecls {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {Esrc : SEnv} {s s' : ErasureState} (h : Erasure.RunConcl s s')
    (hg : ∀ {kn : Kername} {t : LBTerm},
      (kn, GlobalDecl.constantDecl ⟨some t⟩) ∈ s'.gdecls →
      (kn, GlobalDecl.constantDecl ⟨some t⟩) ∈ s.gdecls) :
    RunConclδ env Us Γ Esrc s s' :=
  ⟨h, fun hm => hm.mono_of_gdecls hg⟩

/-! ## Non-vacuity

The run-keyed clauses stay hypothetical, for the same reason `BridgeHyps`' do: they speak
about opaque runtime primitives. What is checked here is that the **scope** half is
satisfiable at a *non-empty* fragment — that `esrc_sub`, `disj` and `nofixvars` are not
true merely because `known` is `⊥`, which is the configuration every cold-start capstone is
pinned to today. -/

section NonVacuity

/-- A one-constant fragment's context: `f` is a plain constant, filed under its canonical
kername, with no constructor, `casesOn` or fixvar role. -/
def gΓδ : ErasureCtx where
  inductives := fun _ => none
  constants := toKername

/-- The source environment of that fragment: `f`'s prepared body, and nothing else. -/
def gEsrcδ (pe : Expr) : SEnv := fun n => if n = `f then some pe else none

@[simp] theorem gEsrcδ_self (pe : Expr) : gEsrcδ pe `f = some pe := by simp [gEsrcδ]

/-- **The fragment is not empty.** `known` holds of `f`, `Esrc` has an entry for it, and
`f` is a plain constant — so the two scope fields below have something to say. -/
theorem gDeltaFragment_nonempty (pe : Expr) :
    (fun n => n = `f) `f ∧ (gEsrcδ pe `f).isSome ∧
      gΓδ.ctors `f = none ∧ gΓδ.casesOns `f = none :=
  ⟨rfl, by simp, rfl, rfl⟩

/-- **The scope half of `DeltaHyps` is satisfiable at that fragment**, and non-vacuously:
`esrc_sub`'s hypothesis is inhabited (`gDeltaFragment_nonempty`) and `disj`'s conclusion is
about a name the fragment really contains. -/
theorem gDeltaScope (pe : Expr) :
    (∀ {n : Name}, (gEsrcδ pe n).isSome → n = `f) ∧
    (∀ {n : Name}, n = `f → gΓδ.ctors n = none ∧ gΓδ.casesOns n = none) ∧
    gΓδ.fixvars = fun _ => none := by
  refine ⟨?_, ?_, rfl⟩
  · intro n hn
    by_cases h : n = `f
    · exact h
    · simp [gEsrcδ, h] at hn
  · rintro n rfl
    exact ⟨rfl, rfl⟩

/-- **The fragment's constant is `Supported`** — the derivation that was unreachable at
`known = ⊥` (`Supported.const` needs `known n`, and `Γ.fixvars = ⊥` kills the other
disjunct). This is what δ-inclusion is *for*. -/
theorem gDeltaSupported : Supported (fun n => n = `f) gΓδ (.const `f []) :=
  .const `f [] (Or.inl rfl) rfl rfl

/-- **Why the registry domain is load-bearing in `get_constant_kername`'s motive.**

At a state where `n` is unregistered the `if let` takes its *miss* branch, and the branch's
result is `s'.constants[n]!` — a `panic!`-defaulting lookup. If the `visitMutual n` call in
between registered nothing, that lookup returns `default`, and `default` is not the
canonical kername of `n`. So the motive-5 conclusion `kn = Γ.constants n` is *false* on a
run whose `visitMutual` does not register, at any `Γ` filing constants canonically: it
cannot be discharged from `Γ`-side or scope-side data alone, and needs either the registry
domain in the state invariant (`BridgeInv.known_dom`, the field slice D4a deleted) or a
registration conclusion in `visitMutual`'s own motive (what D4a put in its place). This is
the exact statement of that gap. -/
theorem constants_get!_unregistered_ne :
    ({} : ErasureState).constants.get? `f = none ∧
      Kername.beq (({} : ErasureState).constants[`f]!) (toKername `f) = false := by
  refine ⟨by simp, ?_⟩
  rw [show (({} : ErasureState).constants[`f]!) = default by simp]
  decide

end NonVacuity

end LeanToLambdaBox
