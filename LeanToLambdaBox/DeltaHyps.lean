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

## The three scope restrictions this bundle makes operational

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
   what lets a δ record transport across every state-growing step that is not a constant
   registration.

## The one residue that is not a scope statement

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
  /-- **No block-local fixvar map** — scope restriction 2. This is the `hnfv` every
  top-level capstone already pins, moved into the bundle because it is exactly what the
  dependency's reader (`withReader (… fixvars := .none …)`) has to agree with. -/
  nofixvars : Γ.fixvars = fun _ => none
  /-- **The declaration fetch agrees with the fragment.** For a `known` name: the fetch is
  generator-monotone, the block is a *single* declaration, it is universe-monomorphic at
  the ambient `Us` (scope restriction 1), and — when it has a value — that value does not
  mention the constant itself (so `visitMutual`'s `nonrecursive` test is forced `true`, and
  the recursive exit is out of scope) and `Esrc` has an entry for the name.

  Stated at the `CoreM` layer, which is the layer `ColdStartRun.run_visitMutual_decomp`
  hands the fetch back at. -/
  decl_run : ∀ {n : Name} {w w₁ : Void IO.RealWorld} {r : Option ConstantInfo},
    known n →
    (Compiler.LCNF.getDeclInfo? n : CoreM (Option ConstantInfo)) cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧ ∃ ci, r = some ci ∧ ci.all = [n] ∧ ci.levelParams = Us ∧
      (∀ v, ci.value? (allowOpaque := true) = some v →
        name_occurs n v = false ∧ (Esrc n).isSome)
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
  once `Erases`/`TrExprS` gain fvar-extension weakening; a premise until then. -/
  uniform : ∀ {n : Name} {pe : Expr} {t : LBTerm} {Δ : VLCtx},
    Esrc n = some pe → Erases env Us Γ [] pe t → Erases env Us Γ Δ pe t

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
  uniform := by intro n pe t Δ h; simp at h

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
