import LeanToLambdaBox.Bridge
import LeanToLambdaBox.ErasesLevels
import LeanToLambdaBox.ErasesUniform
import LeanToLambdaBox.ErasureRun
import LeanToLambdaBox.SourceEval
import Lean4Lean.Verify.NameGenerator

/-!
# The δ-closure bundle: `DeltaHyps`

This structure sits *beside* `BridgeHyps` (`VisitExprRefines.lean`), `DataBridgeHyps`
(`DataBridgeHyps.lean`), `CasesBridgeHyps` (`CasesBridgeHyps.lean`) and `ProjBridgeHyps`
(`ProjBridgeHyps.lean`, slice proj-P8), and carries what it costs to let an erased program
**call** something — the δ (constant-unfolding) fragment.

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
fragment `known`. `RegBridgeHyps` grew three fields at slice proj-P9
(`regProjs`/`regProjFields`, the cold `register_inductive` agreement keyed on `Γ.projs`,
and `satProjs`, its completeness twin) and they are of exactly those two classes — the
first two run-keyed and cold-branch-guarded like `regCases`/`regFields`, the third the
`Γ`-side saturation fact nothing about a run can supply. All the primitives specced here (`Compiler.LCNF.getDeclInfo?`, `getEnv`,
`logInfo`, `Meta.isInstance`, `getConstInfo`, `prepare_erasure`, `addAxiom`) are **real**:
none of them belongs to the `visitExpr` mutual block, so their specs are usable directly
inside `Erasure.visitExpr.mutual_fixpoint_induct`. Because they quantify over opaque
runtime primitives their global satisfiability is not in-logic decidable — the documented
trust boundary, exactly as for
`BridgeHyps`/`DataBridgeHyps`/`CasesBridgeHyps`/`ProjBridgeHyps`.

`mkFreshFVarId` is deliberately **absent**: `BridgeHyps.fresh_run` already specs it, and the
recursive exit's block ids are the only place the registration path mints one.

## Two exits, two bundles

Every clause here is keyed on the **declaration fetch** — `Compiler.LCNF.getDeclInfo?` and
the `prepare_erasure` of its value — because that is what `visitMutual`'s *non-recursive*
exit performs. The **recursive** exit performs a different pair per sibling
(`getConstInfo m` for `m ∈ ci.all`, then `prepare_erasure`), so none of these clauses can
fire there however much they look like they should. `BlockHyps` below is the companion for
that second pair; it is a separate structure so that `of_bot` and the whole non-recursive
path stay untouched and the recursion feature's price stays legible as one ledger row.

## The six scope restrictions this bundle makes operational

They were latent in the development before; here each is a field, so a `Γ`/`known` that
violates one makes the bundle *unsatisfiable* — the right failure mode, but only because it
is written down. The numbering is historical: the live six are 1–4, 6 and 7, and slot 5 is
retired and kept struck below. That fifth — "no fragment constant is recursive"
(`nonrecursive`) — went at slice Γ-W3.6b: it existed only to make `visitMutual`'s
`nonrecursive` test come out `true`, so that the bridge's step 6 could refute the recursive
exit. Step 6 now *walks* that exit, and the field is deleted. See `decl_run`'s docstring for
what took its place (`VisitExprRefines.RecBlockAgreement`, a named premise of the bridge,
not a restriction on the fragment) and `ColdStart`'s `hcov` row for what the trade cost.

The capstones followed at slice Γ-W4: `hnorec : Γ.recBodies = ⊥` is deleted there too, so
**neither this bundle nor the cold-start statements exclude recursion any more**. What the
recursion feature still restricts is one level in and is named at
`RecBlockErasure.erases_rec_block_of_run`: a walked block's bodies call only its own
siblings, registered constructors and registered `casesOn`s.

1. **The dependency cone's level scopes are prefixes of the subject's.** `Erases` is
   indexed by a single `Us`, while `visitMutual` erases a dependency's body under
   `withReader (… lparams := ci.levelParams)`. `decl_run` therefore demands
   `ci.levelParams <+: Us` — **since slice Γ-U2**; before it, the equation
   `ci.levelParams = Us`. At `Us = []`, which is where every capstone runs, the two are
   the same restriction (`gPrefixPin_closed_subject`): universe monomorphism of the whole
   cone. At `Us ≠ []` the prefix admits a *polymorphic subject* whose dependencies are
   declared at a prefix of its scope — in particular every monomorphic dependency of a
   `{u}`-polymorphic caller, which the equation refused. What it still does not admit is a
   **polymorphic dependency of a closed subject** (`[u] <+: []` is false,
   `gPrefixPin_no_polymorphic_dep`): that is the typeclass layer, it needs *instantiation*
   rather than weakening, and it is what Γ-U3/Γ-U4 owe. It was once recorded here that
   this restriction "does not make any theorem *false*"; that is true of *this* bundle and
   false of the development — see the Γ-U analysis below, which is the correction.
2. **No block-local fixvar map, on the fragment.** `Erasure.ErasureContext.fixvars` is
   installed per block while `Γ.fixvars` is a single global map, so one `Γ` cannot be both
   "outside every block" (what a top-level subject needs) and "inside this block" (what a
   recursive dependency's body needs). `nofixvars` pins the first — but since slice δ-D8
   only **on the fragment** (`∀ {n}, known n → …`), which is all its two consumption sites
   ever had in scope. That is what lets the *same* bundle be instantiated a second time at
   the block-local `Γ.withFixvars fv` with `known = ⊥`, which is how the recursive walk
   gets at the bridge without moving `Γ` inside the motives
   (`RecBlockErasure.erases_rec_block_of_run`). The price is a different scope restriction,
   named there: a block body calls only its own siblings, constructors and `casesOn`s.
3. **No fragment constant is emitted as an axiom.** `axiom_free` covers both `addAxiom`
   sites — the value-less and `@[extern] + preferAxiom` exits of `visitMutual` — which is
   what a capstone needs to know that a fragment constant the walk reached really has a
   recorded *body* and not a value-less axiom entry.
4. **Fragment names are distinguished by their kernames.** `Erasure.toKername` is not
   injective, so without `kinj` the δ *record* below is false whenever two fragment names
   collide on a key. It is the fragment-scoped form of the capstone's `hkinj`.
5. ~~**No fragment constant is recursive.**~~ — **RETIRED, slice Γ-W3.6b** (`nonrecursive`,
   the paragraph above). The slot is kept so the numbers the fields below carry keep
   reading.
6. **A fragment body is projection-free at its binders, and translates at the empty
   context.** `esrc_shape`, the S-class residue slice δ-D7b left where the `uniform` field
   had been. **Weakened from `NoProj` to `NoProjBinders` at slice proj-P2**, which is what
   lets the typeclass-dispatch layer into the fragment at all (`OfNat.ofNat`'s prepared
   body is `fun α x self => self.1`); the recursive exit keeps the strong predicate for its
   own siblings (`BlockHyps.block_lam`).
7. **The fragment is closed under block membership, and a block's names are distinct.**
   `decl_run`'s first two conjuncts, and **new in name only at slice Γ-W5**: they replace
   an *unnumbered* and strictly stronger restriction that lived inside the same field —
   `ci.all = [m]`, i.e. no genuine mutual block anywhere in the dependency cone. At arity
   one the new conjuncts are implied by the old pair together with `known n`
   (`gDeclRunMutual_of_single`), so nothing is newly demanded of a self-recursive
   fragment; at arity two and above they are what the recursive walk needs and the old
   pair was simply false (`gDeclRunSingle_mutual_refuted`). The reading is:
   `Compiler.LCNF.getDeclInfo?` answers for a *block*, `visitMutual` erases and registers
   all of it, so a fragment holding one sibling and not the others would have the walk
   register a constant outside its own scope.

## Γ-U — what lifting scope restriction 1 would actually cost (analysis, 2026-08-27)

Restriction 1 is the second uncosted blocker between the fragment and the benchmarks:
every typeclass method is universe-polymorphic (`OfNat.ofNat.{u}`, `HAdd.hAdd.{u,v,w}`,
`Add.add.{u}`, …) while the subjects are `Us = []`, so the projection round's
`Erases.proj` admits `OfNat.ofNat`'s *body* while this field keeps its *declaration*
out. The sketch on record proposed a slice of `Erases`-signature size: state `decl_run`
and `prepared` at `ci.levelParams` and let the consumer transport by `TrExprS.instL`.
**That estimate is wrong, and the reason is worth writing down rather than rediscovering.**
Five findings, in the order a reader will hit them.

**(a) The λ□ side really is level-free, so the transport is entirely `VExpr`-side.**
`Erases env Us Γ Δ e t` mentions `Us` at exactly three constructors — `box`'s
`TrExprS env Us Δ e ve` + `Erasable env Us.length Δ.toCtx ve`, and `lam`/`letE`'s binder
`TrExprS`. Every other premise is a `Γ` lookup, a length side condition or an LBTerm
equation, and `t` never mentions `Us`. The design's guess is confirmed: nothing on the
target side moves.

**(b) Two more fields pin the same restriction, so relaxing `decl_run` alone is a
no-op.** `prepared` demands `∀ Δ, ∃ ve, TrExprS env Us Δ pe ve` and `esrc_shape` demands
`TrExprS env Us [] pe ve` — both at the *ambient* `Us`, both false for a body that
mentions `u` when `Us = []`. A Γ-U bundle has to be indexed by a per-constant map
`Ups : Name → List Name` (with `decl_run` pinning `ci.levelParams = Ups n`), not by a
single relaxed equation.

**(c) There is no composition point outside the induction.** `Us` is a *parameter* of
`VisitExprRefines.visitExpr_refines_erases_core`, not a motive binder, and the
dependency's body is erased by a sub-run **inside** `visitExpr.mutual_fixpoint_induct`
whose result is fed straight to motive 1's own IH (the `BridgeInv` rebuild at
`{ ctx with fixvars := none, lparams := ci.levelParams }`, where `decl_run`'s
`ci.levelParams = Us` fills the `lparams` slot). So the S3/ColdStartDelta
external-composition trick does not apply: the only route is `∀ Us` inside all eighteen
motives, gated by `BridgeInv env Us …`. That gating makes the generalisation *contentless*
— `BridgeInv.lparams : ctx.lparams = Us` determines `Us` from the reader, so at most one
`Us` satisfies the hypothesis — which is the good news; the bad news is 343 occurrences of
`Us` in a 4452-line file plus `BridgeHyps`/`RecBlockAgreement` at `∀ Us`. That is the Γ-W1
pattern at Γ-W1 scale.

**(d) The record composes transitively, so it cannot stay `Us`-indexed.** `DeltaMem`
(below) and `RunConclδ` carry `Us` as a parameter and are chained by `.trans` along the
walk; under a `∀ Us` motive a sub-run at `Us'` cannot hand back a record at the outer
`Us`. `DeltaMem.erase` would have to record at `Ups n` per entry, rippling through
`ErasesEnvDelta`, `ErasesEnvDeltaData`, `RecEnvConsistent`, the three `RegisteredClosure*`
records and `ColdStartDelta`'s six conversions.

**(e) The model's δ step is universe-blind, so this is a change of semantics, not of
scope — and this is the finding that decides the slice.** Every δ rule discards its `us`
and unfolds to the *uninstantiated* body (`SEvalDataι.delta_level_blind`), and subject
reduction discharges the resulting defeq from `SEnvConsistent`, which quantifies `us` and
never mentions it. A real `VEnv` does not supply that: `VEnv.IsDefEq.extra` instantiates
**both** sides of a defining equation, so what it gives is `.const n us ≡ ⟦body⟧.instL us`.
`SEnvConsistent` is therefore the kernel fact only at `instL = id`, and for a polymorphic
constant it is a *stronger*, false demand — it collapses the constant's instantiations
(`SEnvConsistent.levels_collapse`). Relaxing this bundle without repairing that premise
would not widen the fragment: it would move the vacuity from a named, documented field
here into an unnamed premise of the capstones. That is a regression in legibility, and
the reason the slice stopped at analysis rather than landing its cheap half.

**And the repair `TrExprS.instL` offers does not compose with `Erases`.** Upstream's
`TrExprS.instL` lands in `TrExpr`, not `TrExprS` — level *substitution* re-derives sort
and const levels only up to `≈` — while `Erases.box`/`lam`/`letE` record **strict**
`TrExprS` witnesses, and at `lam`/`letE` a defeq-loose binder type breaks the context
chain the sub-derivation runs in. The ι-era `TrExprS.instL_weak` (`IotaPattern`) survives
this only because it transports a *closed* rhs at `Δ = []` and composes the residual defeq
away with `IsDefEqU.mkApps_congr_head`; inside an induction over contexts there is no such
composition point. So `Erases.instL` is not a corollary — it is the wall.

**Plan of record, if the wall is taken.** Four slices, and Γ-U2 must not ship alone:
Γ-U1, a *strict* `TrExprS` scope-weakening along `ci.levelParams <+: Us` (indices are
preserved under a prefix extension, which is why this one can stay strict where `instL`
cannot); Γ-U2, `BridgeInv.lparams` / `decl_run` / `block_lparams` / the oracle premise
relaxed to that prefix, leaving the motives untouched; Γ-U3, `Erases.instL`; Γ-U4, the δ
rule instantiating and `SEnvConsistent` restated at
`body.instantiateLevelParams (Ups n) us`. Γ-U3 is the risk and Γ-U4 is the content.

### Γ-U1 and Γ-U2, landed — and what they did *not* cost (2026-08-28)

`ErasesLevels.lean` (Γ-U1) is the strict weakening kit, premise-free apart from the
prefix; the four pins above now read `<+: Us` (Γ-U2). Four things are worth the ledger,
and the last two are corrections to this analysis.

* **What it buys, exactly**: the *subject* side. At `Us ≠ []` a polymorphic subject may
  call dependencies declared at a prefix of its scope — every monomorphic callee of a
  `{u}`-polymorphic function, and every `{u}`-polymorphic one. What it does **not** buy is
  the dependency side: `OfNat.ofNat.{u}` under a `Us = []` subject stays out, because
  `[u] <+: []` is false. The five guards at the end of this file are that reading,
  machine-checked, together with the refutation that makes it sharp
  (`gEsrcShape_polymorphic_dep_refuted`: at `Us = []` a body mentioning `u` has no
  `TrExprS` at all, so the exclusion is in the *relation*, not in the bundle).
* **It is not a trade for vacuity**, which is the condition the plan attached to it. At
  `Us = []` — every capstone here — `Lp <+: []` *is* `Lp = []` (`gPrefixPin_closed_subject`),
  so no shipped instance weakened and no field became easier to satisfy. The relaxation is
  invisible at the configuration the development ships and live only at one it does not
  yet reach, which is the honest shape for a slice that widens a scope ahead of its
  consumer.
* **Finding (b) does not bite under the prefix reading — the correction.** It said two more
  fields (`prepared`, `esrc_shape`) pin the same restriction at the ambient `Us`, so
  relaxing `decl_run` alone is a no-op. That is right for the *instantiation* reading it
  was written for, and wrong here: at `Lp <+: Us` a producer proves those fields' natural
  own-scope form and `TrExprS.prefix_weaken` carries it to `Us` strictly
  (`gPreparedAtPrefix`). No `Ups` map, no per-constant indexing, and finding (d)'s ripple
  through `DeltaMem`/`RunConclδ` never starts. Findings (c), (d) and (e) are untouched:
  they are about instantiation and they still decide Γ-U3/Γ-U4.
* **The one thing it costs is the oracle, and it is paid where it is visible.**
  `BridgeHyps.orc_run`'s soundness clause is contravariant in `TrExprS` and covariant in
  `Erasable`, so the Γ-U1 kit — which transports upward only — cannot move it in either
  direction; relaxing its guard to `<+: Us` is a strictly larger trust item. The cost is
  localised in `OracleDischarge`: the *verified* kernel branch now carries
  `ctx.lparams = Us` as a conjunct, and a strictly narrower reader falls to the assumed-sound
  `Meta` fallback. At `Us = []` that conjunct is free, so the verified relevance check
  covers exactly what it covered before.

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

## The record, and where the context-uniformity residue went

`DeltaMem` and `RunConclδ` (below) are not hypotheses at all: they are what the bridge
*proves* about a run, and they live here because the bridge's motives mention them.

There used to be a `uniform` field here — the `∀ Δ` context-uniformity residue. It is
gone (slice δ-D7b). The weakening half is a theorem outright
(`ErasesStrengthen.erases_weakFV`/`erases_weak_any`); the strengthening half is
`ErasesUniform.erases_strengthen_closed`, modulo ONE named `VExpr`-level obligation
(`ErasableStrengthen`) that is a premise of the *capstones* rather than a field here,
because it speaks about `env` alone. What this bundle owes it is the S-class `esrc_shape`
field: the fragment's bodies are projection-free *at their binders* (`NoProjBinders`, since
slice proj-P2) and translate at the empty context, which prepared top-level constant bodies
are.
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
    (cfg₀ : ErasureConfig) (Esrc : SEnv) (gw : Void IO.RealWorld → NameGenerator)
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
  /-- **No block-local fixvar map, where it matters** — scope restriction 2, conditioned
  on the fragment (slice δ-D8).

  This is the `hnfv` every top-level capstone already pins, and it lives in the bundle
  because it is exactly what a *dependency's* reader
  (`withReader (… fixvars := .none …)`) has to agree with. That reader is installed by
  `visitMutual`'s **non-recursive** exit, and the bridge reaches it only under
  `known n` — the field's two consumption sites both have that hypothesis in scope. So
  the equation is asked for only on an inhabited fragment.

  Conditioning is what makes the bundle inhabitable at a *block-local*
  `Γ.withFixvars fv` with `known = ⊥`, which is what the recursive walk instantiates the
  bridge at (design §D8): the unconditioned form is outright false there, since
  `(Γ.withFixvars fv).fixvars = fv` is the block's own map. At a top-level `Γ` with an
  inhabited fragment it is the same equation it always was, so no consumer weakens.
  `of_bot` losing its `hnfv` argument is the tell that the field was doing nothing at
  `known = ⊥`. -/
  nofixvars : ∀ {n : Name}, known n → Γ.fixvars = fun _ => none
  /-- **The declaration fetch agrees with the fragment.** For a `known` name: the fetch is
  generator-monotone, the *block* it answers with is one the fragment contains — every
  member's stripped name is `known`, the stripped names are distinct, and the name asked
  for is among them — and its level scope is a **prefix** of the ambient `Us` (scope
  restriction 1, relaxed from `ci.levelParams = Us` at slice Γ-U2).

  It used to carry a fourth conjunct, `(Esrc n).isSome`. Slice D4a made it dead: naming
  *some* body is never enough at the point of use, which needs *this* run's body, and
  `prep_esrc` states that identification directly. Dropping it weakens the bundle, so
  every consumer is unaffected.

  It used to carry a fifth, `name_occurs n v = false` — the recursion exclusion. Slice
  δ-D8e split that out into a field of its own, `nonrecursive`, precisely so that it could
  be *traded* rather than unpicked from a five-conjunct spec; slice Γ-W3.6b traded it. The
  field is **deleted**: the bridge's step 6 now walks the recursive exit
  (`VisitExprRefines.rec_exit_refines_erases`) instead of refuting it, so nothing needs
  the run's `nonrecursive` test to come out `true`. What replaced it is one named premise
  of the bridge, `VisitExprRefines.RecBlockAgreement`, and it is not a fragment
  restriction: a recursive fragment constant is now *in scope*.

  **The names are the block's, not the caller's** (slice Γ-W2), and the difference is the
  whole of what the fragment can contain. `Compiler.LCNF.getDeclInfo?` tries
  `n._unsafe_rec` *before* `n` — it prefers the original recursive definition over the
  elaborated one, which is `visitMutual`'s own comment ("possibly these are
  ._unsafe_rec") — and slice Γ-W0 measured that on this toolchain the arithmetic every
  §H benchmark drags in really does come back that way: `Nat.add`/`mul`/`sub`/`pow`,
  `Nat.ble`/`beq`, `List.length`/`append`/`map`/`foldl` all answer with
  `ci.all = [n._unsafe_rec]`. At `ci.all = [n]` the field was therefore *false* at exactly
  the names the fragment has to contain, and no amount of downstream work could repair
  that. What the field states instead is what the run itself registers under —
  `ci.all.map remove_unsafe_rec` — and `hnmem` identifies the caller's `n` with a member
  of that list. See `rec_exit_registers_stripped_name` and its positive companion below.

  **And the block is no longer a *single* declaration** (slice Γ-W5). Until then the
  conjunct read `ci.all = [m] ∧ remove_unsafe_rec m = n`, which is scope restriction 5':
  self-recursion only, no genuine mutual block anywhere in the dependency cone. The three
  conjuncts that replace it are exactly the three side conditions the recursive walk
  consumes (`VisitExprRefines.rec_exit_refines_erases`' `hkn`/`hnd`/`hnmem`), and they are
  *implied* by the old pair together with the field's own `known n` premise — so this is a
  relaxation, not a trade: `gDeclRunMutual_of_single` checks the implication, and
  `gDeclRunMutual` checks that the new form is inhabited by a genuine two-member block,
  which the old one refutes (`gDeclRunSingle_mutual_refuted`).

  What the three conjuncts *mean* is the block-scope closure condition the recursion
  feature always had, now stated where it is used rather than assumed away:

  * `∀ m ∈ ci.all, known (remove_unsafe_rec m)` — **the fragment is closed under block
    membership.** `getDeclInfo?` answers for a *block*, and `visitMutual` erases and
    registers all of it; a fragment containing one sibling and not the others would make
    the walk register a constant outside its own scope. This is the honest reading of
    "what does the fetch return for a member of a mutual block": `ci.all` lists *every*
    member, so the fragment has to as well;
  * `(ci.all.map remove_unsafe_rec).Nodup` — the block's own names are distinct after
    stripping. Nothing in `ConstantInfo` says so (`all` is a plain `List Name`), and the
    walk needs it twice: `mkDef`'s fold looks each sibling up in the block map, and the
    registration `forIn` files one entry per stripped name;
  * `n ∈ ci.all.map remove_unsafe_rec` — the caller's name is one the exit registers. At a
    single declaration this is `remove_unsafe_rec m = n`, verbatim; at a mutual block it is
    the same fact about whichever sibling was asked for.

  Stated at the `CoreM` layer, which is the layer `ColdStartRun.run_visitMutual_decomp`
  hands the fetch back at. -/
  decl_run : ∀ {n : Name} {w w₁ : Void IO.RealWorld} {r : Option ConstantInfo},
    known n →
    (Compiler.LCNF.getDeclInfo? n : CoreM (Option ConstantInfo)) cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧ ∃ ci : ConstantInfo,
      r = some ci ∧ (∀ m ∈ ci.all, known (remove_unsafe_rec m)) ∧
      (ci.all.map remove_unsafe_rec).Nodup ∧ n ∈ ci.all.map remove_unsafe_rec ∧
      ci.levelParams <+: Us
  /-- **The prepared dependency body is in the fragment.** Quantified over the
  `prepare_erasure` run that produces it, exactly as `ColdStartSubject.supported` is for the
  top-level subject: this is the *same* premise, generalised from "the subject" to "the
  subject and every constant it calls", and it should be read in one breath with that one
  rather than as a second, independent restriction. The `Supported` half is a genuine
  fragment restriction (no `.proj`, no η-contracted minors, no machine `Nat`); the `∀ Δ` on
  the translatability is what the two-sided context transport consumes — see `esrc_shape`,
  and `ErasesUniform.erases_uniform_closed` for the transport itself. (Slice δ-D7a
  corrected the reason once given here: `TrExprS.weakFV` is *not* missing upstream.)

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
  induction there is no composition site to take it at.

  **The reader is gated on the bundle's own config** (slice Γ-W3.6a), and that is a
  strict strengthening of the *field* — i.e. a weakening of what a producer must
  believe. `prepare_erasure`'s output genuinely depends on `ctx.config.csimp`
  (`Erasure.lean`'s csimp branch), so the clause as it shipped at Γ-W2 quantified `ctx`
  over readers that prepare **different** bodies and pinned all of them to one `Esrc n`
  — contradictory for any `Esrc` if two admissible configs disagree. The new premise
  `ctx.config = cfg₀` removes exactly that: the field now speaks about one config, the
  one the bundle is stated at. Nothing is lost at the point of use, because every
  consumer holds a `BridgeInv` and reads the equation off `BridgeInv.cfg`. What stays
  quantified — `ctx.lctx`, the state and the world — is reader data
  `prepare_erasure` is transparent in, plus the development's standing world boundary. -/
  prep_esrc : ∀ {n : Name} {ci : ConstantInfo} {r : Option ConstantInfo} {v pe : Expr}
      {s s₁ : ErasureState} {ctx : ErasureContext}
      {wd wd₁ w w₁ : Void IO.RealWorld},
    known n →
    (Compiler.LCNF.getDeclInfo? n : CoreM (Option ConstantInfo)) cctx ref wd = .ok r wd₁ →
    r = some ci → ci.value? (allowOpaque := true) = some v →
    prepare_erasure v s ctx cctx ref w = .ok (pe, s₁) w₁ →
    ctx.config = cfg₀ →
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
  /-- **A fragment body is projection-free *at its binders* and translates at the empty
  context** — scope restriction 6, and an S-class fact about a *prepared top-level constant
  body*, which every one of them is. Closedness and fvar-freeness are not separate demands:
  both follow from the `TrExprS` witness (`TrExprS.closed`/`TrExprS.fvarsIn`).
  `NoProjBinders` is what pins that witness where the context transport needs it pinned:
  at a λ/∀ binder's type and a `let`'s type and value, the three positions
  `Erases.strengthen_fvlift_binders` spends uniqueness on.

  **Weakened from `NoProj` at slice P2, and that is the point of the slice.** `NoProj`
  excluded `.proj` *anywhere*, so the entire typeclass-dispatch layer was outside the
  fragment — `OfNat.ofNat`'s prepared body is `fun α x self => self.1` — no matter what
  `Erases` could derive for it (slice P1 gave it a `proj` rule). `NoProjBinders` admits
  exactly those bodies and nothing whose *binders* mention a projection, which is the
  boundary equational uniqueness draws: uniqueness at `.proj` is false, not unproved.
  See `ErasesUniform.NoProjBinders`, and `ErasesUniform.noProjBinders_ofNatBody` /
  `noProj_ofNatBody_refuted` for the two halves of the guard. The residual cut is
  `let y := self.1; …`, still outside; the recursive exit keeps the strong predicate for
  its own siblings (`BlockHyps.block_lam`).

  [Provenance corrected at the `fee3ada` re-pin, 2026-08-27: this used to read
  "lean4lean's `TrProj` is `sorry` upstream". `TrProj` now has a real definition; what is
  still `sorry` is `TrProj.uniq` specifically, one of the three remaining `PROJ-TODO`s
  (`ColdStart.lean`'s trio). That
  is the route the weakened field pays for — `erases_strengthen_closed` consumed it
  already, so no axiom set moved at P2.]

  This field replaces the old `uniform` residue (slice δ-D7b). Context-uniformity is now a
  theorem (`ErasesUniform.erases_strengthen_closed` composed with
  `ErasesStrengthen.erases_weak_any`) rather than a premise; what those need of the source
  they transport is exactly this, and it is a property of the term, not of the erasure.
  The single named `VExpr`-level obligation that remains — `ErasableStrengthen` — is a
  premise of the *capstones*, not a field here, because it speaks about `env` alone and is
  commissioned upstream. -/
  esrc_shape : ∀ {n : Name} {pe : Expr}, Esrc n = some pe →
    NoProjBinders pe ∧ ∃ ve, TrExprS env Us [] pe ve

/-- **What the bundle costs at the empty fragment** — the honest accounting for every
consumer that runs at `known = ⊥` (the block instantiation and the `known = ⊥` guards; it
was *all* of them until the capstone rewiring of slices δ-D5/δ-D6).

The *scope* half is free there and is discharged below: `esrc_sub`, `disj`, `kinj`,
`decl_run`, `prepared`, `prep_esrc` and `esrc_shape` all have `known n` or
`(Esrc n).isSome`
in their premises, and `axiom_free`'s conclusion is `none = none`. Since slice δ-D8 `nofixvars`
joins them — it is conditioned on `known n` too, which is why this lemma no longer takes
an `hnfv` argument and why the bundle is inhabitable at a *block-local* `Γ`. The
*bookkeeping* half is **not** free and is passed in:
`log_run`/`env_run`/`inst_run`/`ci_run`/`prep_run` are
generator-monotonicity (and, for `prep_run`, state-transparency) statements about real
primitives, and `gw` is an arbitrary map from world tokens to generators — nothing in the
logic makes `gw w ≤ gw w'` hold across a world-advancing call. They are the same
epistemic class as `BridgeHyps.fresh_run`, which is why `BridgeHyps` assumes its four and
this bundle its five.

So: a `known = ⊥` consumer buys exactly five things, and no `Γ`-side or fragment-scope
obligation at all. -/
theorem DeltaHyps.of_bot {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {cfg₀ : ErasureConfig}
    {gw : Void IO.RealWorld → NameGenerator} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State}
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
    DeltaHyps env Us (fun _ => False) Γ cfg₀ (fun _ => none) gw cctx ref where
  esrc_sub := by intro n h; simp at h
  disj := fun h => h.elim
  kinj := fun h => h.elim
  nofixvars := fun h => h.elim
  decl_run := fun h => h.elim
  prepared := fun h => h.elim
  prep_esrc := fun h => h.elim
  axiom_free := fun _ => rfl
  log_run := hlog
  env_run := henv
  inst_run := hinst
  ci_run := hci
  prep_run := hprep
  esrc_shape := by intro n pe h; simp at h

/-! ## The block-local companion: `BlockHyps`

`DeltaHyps` is keyed on the **declaration fetch** — `Compiler.LCNF.getDeclInfo?` followed
by `prepare_erasure` — because that is the pair of runs `visitMutual`'s *non-recursive*
exit performs. The **recursive** exit performs a different pair, once per sibling:
`getConstInfo m` for `m ∈ ci.all`, then `prepare_erasure (ci.value! …)`
(`Erasure.visitMutual`). Different runs, different key: `decl_run`/`prep_esrc` cannot fire
there, however much they look like they should.

What follows is the companion bundle for that second pair. It is a *separate* structure
rather than five more `DeltaHyps` fields for three reasons: `DeltaHyps.of_bot` and the
whole non-recursive path stay untouched, the recursion feature's price is legible as one
ledger row, and it is where the `ErasableStrengthen` residue belongs — visibly attached to
recursion rather than smuggled into the δ bundle every cold start already pays.

### The keying, and why it is not the obvious one

Every run-keyed field below reads `known (remove_unsafe_rec m)`, **not** `known m`. The
loop's `m` ranges over `ci.all`, and slice Γ-W0 measured that on this toolchain those are
`._unsafe_rec` names for exactly the declarations the fragment must contain
(`Nat.add`/`mul`/`sub`/`pow`, `Nat.ble`/`beq`, `List.length`/`append`/`map`/`foldl`). The
fragment `known` contains the plain names — that is what `visitMutual`'s caller asks for
and what the exit registers under. Keyed on `known m` every field here would be
**vacuous** on precisely the data the slice exists to cover; `gBlockKeying` is that check.

### What is *not* a field, and why

The design this implements listed seven fields. Four of them turned out to be consequences
of what the walk already carries, and are proved rather than assumed
(`BlockHyps.sibling_scope`):

* `block_prepared` — `Supported known Γ₀ pe` and the `∀ Δ` translatability. `DeltaHyps.prepared`
  is keyed on *any* `prepare_erasure` run producing `pe` plus `Esrc n = some pe`, and the
  block loop holds both (the second from `block_esrc`). It fires unchanged;
* `block_shape`'s closedness and fvar-freeness — consequences of the `TrExprS` witness
  (`TrExprS.closed`, `TrExprS.fvarsIn`), which is what `DeltaHyps.esrc_shape` already
  supplies, keyed on `Esrc n = some pe` alone;
* `block_shape`'s empty-context translation — `DeltaHyps.esrc_shape`, verbatim. Its
  `NoProj` came from there too until slice P2 weakened that field to `NoProjBinders`; it is
  now the second conjunct of `block_lam`, for the trust reason spelled out there;
* `stripped` (`known n → remove_unsafe_rec n = n`) — the fragment restriction slice δ-D8e
  predicted the recursive exit would cost. It does not: the relaxed `decl_run` supplies
  `n ∈ ci.all.map remove_unsafe_rec` for the *fetched* block, which is the fact the
  registration actually needs, and it is true where `stripped` plus the old `decl_run` was
  jointly unsatisfiable. See `rec_exit_registers_name` and, at arity two,
  `gRecExitRegistersBoth`.

So one genuine scope field survives — the sibling body is a projection-free λ, neither
half of which any `TrExprS` witness implies — beside two run-keyed clauses and two
residues. -/

/-- **What the recursive exit's siblings cost.** Two Hoare clauses for the block loop's own
runs, one scope fact, and the two residues recursion drags in.

Epistemic class, field by field: `block_lparams` and `block_esrc` are H+S in the same sense
as `DeltaHyps`' run-keyed clauses (specs for real primitives, conditioned on the fragment);
`block_lam` is S; `strengthen` is the development's single class-R residue, already a
premise of both cold-start capstones, and appears here because the `Δ → []` strengthening
of a sibling body happens *inside* the bridge induction; `nonest` is S — unreachable in the
intended use, since the shipping eraser never nests a block inside a body (the standing
residue recorded at `RecBlockErasure.Erases.instFixvars`). -/
structure BlockHyps (env : VEnv) (Us : List Name) (known : Name → Prop) (Γ₀ : ErasureCtx)
    (cfg₀ : ErasureConfig) (Esrc : SEnv)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State) : Prop where
  /-- **The block's level scope is a prefix of the ambient one**, at the loop's own fetch —
  scope restriction 1 for `getConstInfo` rather than `getDeclInfo?`. This is what feeds
  `BridgeInv.withFixvars`' `hlp` slot when the per-sibling invariant is rebuilt: the exit's
  inner `withReader (… lparams := ci.levelParams)` has to land back inside the ambient `Us`.
  `DeltaHyps.decl_run`'s own prefix conjunct is about the *outer* fetch and says nothing
  about the siblings'.

  **Relaxed from `ci.levelParams = Us` at slice Γ-U2**, in step with `decl_run` and
  `BridgeInv.lparams`; at `Us = []` the two forms coincide. -/
  block_lparams : ∀ {m : Name} {ci : ConstantInfo} {s s' : ErasureState}
      {ctx : ErasureContext} {w w' : Void IO.RealWorld},
    known (remove_unsafe_rec m) →
    (getConstInfo m : EraseM ConstantInfo) s ctx cctx ref w = .ok (ci, s') w' →
    ci.levelParams <+: Us
  /-- **`Esrc` records the sibling's prepared body** — the block analogue of `prep_esrc`,
  keyed on the two runs a caller inside the loop actually holds, and landing at the
  *stripped* name because that is the one the fragment and the registration use.

  Gated on the bundle's config since slice Γ-W3.6a, for the reason spelled out at
  `DeltaHyps.prep_esrc`: the preparing reader's `csimp` selects which body comes back, so
  an ungated `∀ ctx` pins two different bodies to one `Esrc` entry. The block loop's
  reader is `blockReader … ctx` with the sibling's `lparams` on top, and
  `RecBlockErasure.blockReader_config` is `rfl`, so the consumer discharges the premise
  with `BridgeInv.cfg` unchanged. -/
  block_esrc : ∀ {m : Name} {ci : ConstantInfo} {pe : Expr}
      {sc s s₁ : ErasureState} {ctx ctx' : ErasureContext}
      {wc wc' w w₁ : Void IO.RealWorld},
    known (remove_unsafe_rec m) →
    (getConstInfo m : EraseM ConstantInfo) sc ctx' cctx ref wc = .ok (ci, s) wc' →
    prepare_erasure (ci.value! (allowOpaque := true)) s ctx cctx ref w = .ok (pe, s₁) w₁ →
    ctx.config = cfg₀ →
    Esrc (remove_unsafe_rec m) = some pe
  /-- **A block source is a projection-free λ.** `erases_rec_block_of_run`'s `hsrc`, and
  the shape facts no `TrExprS` witness gives. Closedness, fvar-freeness and the
  empty-context translation still come from `DeltaHyps.esrc_shape`
  (`BlockHyps.sibling_scope`); the two conjuncts here are:

  * **λ-headedness** — a prepared top-level *recursive definition* body is a λ telescope,
    which is what makes the block's `mkDef` fold meaningful;
  * **`NoProj`** — projection-freeness *everywhere*, which slice P2 moved here out of
    `DeltaHyps.esrc_shape` when that field weakened to `NoProjBinders`. The sibling loop
    strengthens each body from the call site's `Δ` to `[]` inside the bridge induction, and
    the strengthening that runs at the weak predicate
    (`ErasesUniform.Erases.strengthen_fvlift_binders`) buys the relaxation with
    `TrProj.uniq`'s `sorryAx`, while the equational one
    (`ErasesUniform.Erases.strengthen_fvlift`) is `sorryAx`-free. Keeping the strong
    predicate on this path is what keeps `VisitExprRefines.rec_exit_refines_erases` — and
    with it the bridge — clean: the projection round's trust cost lands on
    `erases_strengthen_closed`, which carried that `sorryAx` already, and nowhere else.
    Nothing is newly assumed either: this is the *same* condition `esrc_shape` demanded of
    every fragment body before P2, now demanded only of the recursive ones. Lifting it is
    the natural follow-on slice — it costs exactly the axiom movement described above. -/
  block_lam : ∀ {m : Name} {pe : Expr}, known m → Esrc m = some pe →
    NoProj pe ∧ ∃ n ty b bi, pe = .lam n ty b bi
  /-- **The `Δ → []` strengthening the block needs.** The loop erases each sibling at the
  *call site's* `Δ` — `visitMutual`'s `withReader` moves `fixvars` and `lparams` and leaves
  the `lctx` alone — while `erases_rec_block_of_run`'s `hopen` demands the erasure at `[]`.
  The bridge is `ErasesUniform.erases_strengthen_closed`, whose only named obligation is
  this one. It is already a premise of both cold-start capstones, so no ledger row is
  added; it sits here rather than in `DeltaHyps` so that the accounting stays honest about
  *which feature* drags the development's one class-R residue into the induction. -/
  strengthen : ErasableStrengthen env Us
  /-- **The `Erases.instFixvars` residue** (`RecBlockErasure`), unreachable in the intended
  use: the shipping eraser never nests a `.fix` inside a body, so no derivation at the
  block-local context ever has to be replayed at the ambient one. Quantified over the block
  map `fv`, because the induction meets it at whatever map the run installed. -/
  nonest : ∀ {fv : Name → Option FVarId} {Δ' : VLCtx} {n' : Name} {ty' b' : Expr}
      {bi' : BinderInfo} {d' : List (@FixDef LBTerm)} {i' : Nat},
    Erases env Us (Γ₀.withFixvars fv) Δ' (.lam n' ty' b' bi') (.fix d' i') →
    Erases env Us Γ₀ Δ' (.lam n' ty' b' bi') (.fix d' i')

/-- **What the block bundle costs at the empty fragment** — the mirror of
`DeltaHyps.of_bot`, and the tell that the scope half is genuinely fragment-scoped.

All three fragment-keyed fields are free at `known = ⊥`, at *any* `Esrc`: the two run
clauses ask for `known (remove_unsafe_rec m)` and `block_lam` for `known m`. What a
`known = ⊥` consumer buys is exactly the two residues — which is the honest price of the
recursion feature, and it is two, not seven. -/
theorem BlockHyps.of_bot {env : VEnv} {Us : List Name} {Γ₀ : ErasureCtx}
    {cfg₀ : ErasureConfig} {Esrc : SEnv}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    (hstr : ErasableStrengthen env Us)
    (hnest : ∀ {fv : Name → Option FVarId} {Δ' : VLCtx} {n' : Name} {ty' b' : Expr}
        {bi' : BinderInfo} {d' : List (@FixDef LBTerm)} {i' : Nat},
      Erases env Us (Γ₀.withFixvars fv) Δ' (.lam n' ty' b' bi') (.fix d' i') →
      Erases env Us Γ₀ Δ' (.lam n' ty' b' bi') (.fix d' i')) :
    BlockHyps env Us (fun _ => False) Γ₀ cfg₀ Esrc cctx ref where
  block_lparams := fun h => h.elim
  block_esrc := fun h => h.elim
  block_lam := fun h => h.elim
  strengthen := hstr
  nonest := hnest

/-- **The sibling's scope package, assembled** — every fact
`RecBlockErasure.erases_rec_block_of_run` asks of one block source, from the two runs the
loop hands back.

This is where the design's `block_prepared` and `block_shape` went. Only the λ-headedness
and `NoProj` come from `BlockHyps` (`block_lam`; the second of the two moved there at slice
P2, when `esrc_shape` weakened to `NoProjBinders`); `Supported`, the `∀ Δ` translatability
and the empty-context witness are `DeltaHyps`' existing `prepared`/`esrc_shape`, and
closedness and fvar-freeness are read off that witness (`TrExprS.closed`,
`TrExprS.fvarsIn`) rather than assumed. Stating it as one theorem is what keeps the two
bundles' division of labour checkable: if a conjunct here ever stops being derivable, this
is the line that breaks. -/
theorem BlockHyps.sibling_scope {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ₀ : ErasureCtx} {cfg₀ : ErasureConfig} {Esrc : SEnv}
    {gw : Void IO.RealWorld → NameGenerator}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    (Hβ : BlockHyps env Us known Γ₀ cfg₀ Esrc cctx ref)
    (Hδ : DeltaHyps env Us known Γ₀ cfg₀ Esrc gw cctx ref)
    {m : Name} {ci : ConstantInfo} {pe : Expr}
    {sc s s₁ : ErasureState} {ctx ctx' : ErasureContext}
    {wc wc' w w₁ : Void IO.RealWorld}
    (hkn : known (remove_unsafe_rec m))
    (hci : (getConstInfo m : EraseM ConstantInfo) sc ctx' cctx ref wc = .ok (ci, s) wc')
    (hpr : prepare_erasure (ci.value! (allowOpaque := true)) s ctx cctx ref w
             = .ok (pe, s₁) w₁)
    (hcfg : ctx.config = cfg₀) :
    Esrc (remove_unsafe_rec m) = some pe ∧
      Supported known Γ₀ pe ∧ (∀ Δ : VLCtx, ∃ ve, TrExprS env Us Δ pe ve) ∧
      (∃ n ty b bi, pe = .lam n ty b bi) ∧
      pe.Closed 0 ∧ FVarsIn (fun _ => False) pe ∧
      NoProj pe ∧ (∃ ve, TrExprS env Us [] pe ve) := by
  have hlink : Esrc (remove_unsafe_rec m) = some pe := Hβ.block_esrc hkn hci hpr hcfg
  obtain ⟨hsupp, htr⟩ := Hδ.prepared hkn hlink hpr
  obtain ⟨-, ve, hve⟩ := Hδ.esrc_shape hlink
  obtain ⟨hnp, hlam⟩ := Hβ.block_lam hkn hlink
  refine ⟨hlink, hsupp, htr, hlam, ?_, ?_, hnp, ve, hve⟩
  · simpa [VLCtx.bvars] using hve.closed
  · exact hve.fvarsIn.mono (by simp)

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
* **`∃ Δ`, not `∀ Δ`, and the `Δ` comes with its papers.** The bridge fires at the `Δ` of
  the *call site*, and `visitMutual`'s `withReader` keeps the ambient `lctx`, so a
  dependency reached from inside a binder is genuinely erased at a non-empty `Δ`. Lifting
  to `∀ Δ` is context-uniformity, and since slice δ-D7b that is a *theorem*
  (`ErasesUniform.erases_uniform_closed`) rather than the `uniform` premise — but it needs
  two facts about the context it starts from: that it is well-formed and that it has no
  bvar entries (so `VLCtx.FVLift.from_nil` applies). Both are free at the production site,
  from `BridgeInv.vlctx_wf` and `BridgeInv.noBV`, and recording them here is what lets the
  capstone consume the record without re-deriving them from a run it no longer holds. -/
structure DeltaMem (env : VEnv) (Us : List Name) (Γ : ErasureCtx) (Esrc : SEnv)
    (s : ErasureState) : Prop where
  erase : ∀ {n : Name} {body : Expr} {t : LBTerm}, Esrc n = some body →
    (Γ.constants n, GlobalDecl.constantDecl ⟨some t⟩) ∈ s.gdecls →
    ∃ Δ : VLCtx, VLCtx.WF env Us.length Δ ∧ Δ.NoBV ∧ Erases env Us Γ Δ body t

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
    (hwit : ∀ {body : Expr}, Esrc n = some body →
      ∃ Δ : VLCtx, VLCtx.WF env Us.length Δ ∧ Δ.NoBV ∧ Erases env Us Γ Δ body t) :
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

/-- Membership in `List.zipIdx` read back as an index-with-bound. -/
private theorem zipIdx_mem_index {α : Type _} {l : List α} {a : α} {i : Nat}
    (h : (a, i) ∈ l.zipIdx) : ∃ hi : i < l.length, l[i]'hi = a := by
  have hg : l[i]? = some a := List.mk_mem_zipIdx_iff_getElem?.mp h
  have hlt : i < l.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hg
    simp at hg
  exact ⟨hlt, by rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some.inj hg⟩

/-- The block registration, one sibling at a time. `Erasure.recConstState` is a `foldl` of
`Erasure.recConstStep`, which *is* the non-recursive cons at a `.fix` body, so the block
extension is `DeltaMem.nonrec` iterated. Stated over an arbitrary `(name, index)` list so
the fold has something to generalise over. -/
private theorem DeltaMem.recBlockAux {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {Esrc : SEnv} {defs : List (@FixDef LBTerm)} :
    ∀ (L : List (Name × Nat)) (s : ErasureState), DeltaMem env Us Γ Esrc s →
      (∀ p ∈ L, Γ.constants p.1 = toKername p.1) →
      (∀ p ∈ L, ∀ {m : Name}, (Esrc m).isSome → Γ.constants m = Γ.constants p.1 → m = p.1) →
      (∀ p ∈ L, ∀ {body : Expr}, Esrc p.1 = some body →
        ∃ Δ : VLCtx, VLCtx.WF env Us.length Δ ∧ Δ.NoBV ∧
          Erases env Us Γ Δ body (.fix defs p.2)) →
      DeltaMem env Us Γ Esrc (L.foldl (Erasure.recConstStep defs) s)
  | [], _, h, _, _, _ => h
  | p :: rest, s, h, hkn, hinj, hwit =>
    DeltaMem.recBlockAux rest _
      (h.nonrec (hkn p (by simp)) (hinj p (by simp)) (hwit p (by simp)))
      (fun q hq => hkn q (by simp [hq])) (fun q hq => hinj q (by simp [hq]))
      (fun q hq => hwit q (by simp [hq]))

/-- **The other extension step** (recursion wall, slice Γ-W0). The recursive exit conses one
`.fix` entry per sibling, all sharing the *same* block `defs` and differing only in the
index; the record grows by the whole block at once.

The mirror of `DeltaMem.nonrec`, premise for premise: `hkn` is `BridgeInv.knames` at each
sibling, `hinj` is `DeltaHyps.kinj` composed with `esrc_sub`, and `hwit` is the `Erases.fix`
derivation the recursive exit's run supplies (`RecBlockErasure.erases_rec_block_of_run`),
whose conclusion is already `∀ Δ` — so the record's `∃ Δ` is met at whatever context the
caller has, `[]` included, where the well-formedness and `NoBV` conjuncts are trivial. -/
theorem DeltaMem.recBlock {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Esrc : SEnv}
    {s : ErasureState} {fixnames : List Name} {defs : List (@FixDef LBTerm)}
    (h : DeltaMem env Us Γ Esrc s)
    (hkn : ∀ (j : Nat) (hj : j < fixnames.length),
      Γ.constants (fixnames[j]'hj) = toKername (fixnames[j]'hj))
    (hinj : ∀ (j : Nat) (hj : j < fixnames.length) {m : Name}, (Esrc m).isSome →
      Γ.constants m = Γ.constants (fixnames[j]'hj) → m = fixnames[j]'hj)
    (hwit : ∀ (j : Nat) (hj : j < fixnames.length) {body : Expr},
      Esrc (fixnames[j]'hj) = some body →
      ∃ Δ : VLCtx, VLCtx.WF env Us.length Δ ∧ Δ.NoBV ∧
        Erases env Us Γ Δ body (.fix defs j)) :
    DeltaMem env Us Γ Esrc (Erasure.recConstState fixnames defs s) := by
  rw [Erasure.recConstState_eq]
  refine DeltaMem.recBlockAux _ _ h ?_ ?_ ?_
  · rintro ⟨nm, i⟩ hp
    obtain ⟨hlt, rfl⟩ := zipIdx_mem_index hp
    exact hkn i hlt
  · rintro ⟨nm, i⟩ hp
    obtain ⟨hlt, rfl⟩ := zipIdx_mem_index hp
    intro m hs he
    exact hinj i hlt hs he
  · rintro ⟨nm, i⟩ hp
    obtain ⟨hlt, rfl⟩ := zipIdx_mem_index hp
    intro body hb
    exact hwit i hlt hb

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
    (hwit : ∀ {body : Expr}, Esrc n = some body →
      ∃ Δ : VLCtx, VLCtx.WF env Us.length Δ ∧ Δ.NoBV ∧ Erases env Us Γ Δ body t) :
    RunConclδ env Us Γ Esrc s (Erasure.nonrecConstState n t s) :=
  ⟨Erasure.runConcl_nonrecConstState n t s, fun h => h.nonrec hkn hinj hwit⟩

/-- The recursive exit's registration delta, as a `RunConclδ` step (recursion wall, slice
Γ-W0). The `RunConcl` half is `Erasure.runConcl_recConstState`; the δ half is
`DeltaMem.recBlock`. -/
theorem RunConclδ.recBlock {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Esrc : SEnv}
    {s : ErasureState} {fixnames : List Name} {defs : List (@FixDef LBTerm)}
    (hkn : ∀ (j : Nat) (hj : j < fixnames.length),
      Γ.constants (fixnames[j]'hj) = toKername (fixnames[j]'hj))
    (hinj : ∀ (j : Nat) (hj : j < fixnames.length) {m : Name}, (Esrc m).isSome →
      Γ.constants m = Γ.constants (fixnames[j]'hj) → m = fixnames[j]'hj)
    (hwit : ∀ (j : Nat) (hj : j < fixnames.length) {body : Expr},
      Esrc (fixnames[j]'hj) = some body →
      ∃ Δ : VLCtx, VLCtx.WF env Us.length Δ ∧ Δ.NoBV ∧
        Erases env Us Γ Δ body (.fix defs j)) :
    RunConclδ env Us Γ Esrc s (Erasure.recConstState fixnames defs s) :=
  ⟨Erasure.runConcl_recConstState fixnames defs s, fun h => h.recBlock hkn hinj hwit⟩

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
true merely because `known` is `⊥`, which is the configuration the block instantiation and
the `known = ⊥` guards stand at, and the one every cold-start capstone was pinned to until
slice δ-D5. -/

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
    (∀ {n : Name}, n = `f → gΓδ.fixvars = fun _ => none) := by
  refine ⟨?_, ?_, fun _ => rfl⟩
  · intro n hn
    by_cases h : n = `f
    · exact h
    · simp [gEsrcδ, h] at hn
  · rintro n rfl
    exact ⟨rfl, rfl⟩

/-- **The conditioning is load-bearing** (slice δ-D8): at a **block-local** `Γ` — one
carrying the fixvar map `visitMutual` installs — the *unconditioned* `nofixvars` is
outright false, while the conditioned field is free at `known = ⊥`. That is the whole
content of the change: it is what lets the recursive walk instantiate the same bundle a
second time inside the block (`RecBlockErasure.erases_rec_block_of_run`) instead of moving
`Γ` inside the bridge's eighteen motives. -/
theorem gNofixvars_blocklocal_refuted (x : FVarId) :
    ¬ (gΓδ.withFixvars (fun n => if n = `f then some x else none)).fixvars
        = fun _ => none := by
  intro h
  have := congrFun h `f
  simp at this

/-- …and the conditioned field *is* satisfiable there — vacuously, which is the point:
`known = ⊥` inside a block, so nothing in the bundle ever asks for the equation. -/
theorem gNofixvars_blocklocal (x : FVarId) :
    ∀ {n : Name}, (fun _ => False) n →
      (gΓδ.withFixvars (fun m => if m = `f then some x else none)).fixvars
        = fun _ => none :=
  fun h => h.elim

/-- **The recursive exit registers under the *stripped* name, on real data**
(slice δ-D8e; re-read at Γ-W2).

`visitMutual`'s recursive exit registers under `names.map remove_unsafe_rec`, not under
`names`: the loop is `for (n, i) in fixvarnames.zipIdx do … constants.insert n (toKername n)`
with `fixvarnames := names.map remove_unsafe_rec` (`Erasure.lean`). Motive 6's conclusion
is `(s'.constants.get? n).isSome` at the name the *caller* asked for, so the two names have
to be the same one — and this theorem is the check that they are genuinely different names
when the fetch answers with an `._unsafe_rec` declaration, which is the shape
`Compiler.LCNF.getDeclInfo?` hands back whenever it prefers the original recursive
definition over the elaborated one (`Erasure.visitMutual`'s own comment, "possibly these
are ._unsafe_rec").

**What slice δ-D8e concluded from it was wrong in its direction** (corrected at Γ-W2). It
read this as a further *fragment* restriction — `remove_unsafe_rec n = n` for every
`known n`, to be paid as a new field — and that reading has the arrow backwards. The
caller's `n` is the plain name; what carries the `._unsafe_rec` suffix is the *fetched*
declaration's `ci.all`, which the old `decl_run` conjunct `ci.all = [n]` wrongly pinned to
the caller's name. Under the relaxed field the registration happens under
`ci.all.map remove_unsafe_rec`, a list the caller's `n` is a *member* of
(`decl_run`'s `hnmem`; at Γ-W2 the same fact read `remove_unsafe_rec m = n`, its arity-one
form): no fragment restriction is bought, and the fragment gains every name whose
declaration comes back suffixed — which slice Γ-W0 measured to be all of the §H
benchmarks' arithmetic. `rec_exit_registers_name` below is that reading, on the same data,
and `gRecExitRegistersBoth` is its arity-two twin. -/
theorem rec_exit_registers_stripped_name (defs : List (@FixDef LBTerm)) :
    remove_unsafe_rec (`f ++ `_unsafe_rec) = `f ∧
      ((recConstState [remove_unsafe_rec (`f ++ `_unsafe_rec)] defs {}).constants.get?
        (`f ++ `_unsafe_rec)) = none := by
  refine ⟨by decide, ?_⟩
  simp [recConstState,
    show ¬ remove_unsafe_rec (`f ++ `_unsafe_rec) = `f ++ `_unsafe_rec by decide]

/-- **…and the same run registers exactly the name the caller asked for** (slice Γ-W2) —
the positive half, and the reason the relaxed `DeltaHyps.decl_run` costs the fragment
nothing.

`visitMutual f` fetches `ci` with `ci.all = [f._unsafe_rec]` (the measured shape), enters
the single-declaration prefix because the run's own test is `ci.all.length == 1`, and
registers under `ci.all.map remove_unsafe_rec = [f]`. So motive 6's registration
conclusion at the caller's `f` holds on the nose. Both halves of that sentence are checked
here: the length test the run performs, and the registry hit at `f`. -/
theorem rec_exit_registers_name (defs : List (@FixDef LBTerm)) :
    ([`f ++ `_unsafe_rec].length == 1) = true ∧
      ((recConstState ([`f ++ `_unsafe_rec].map remove_unsafe_rec) defs {}).constants.get?
        `f).isSome := by
  refine ⟨by decide, ?_⟩
  simp [recConstState, show remove_unsafe_rec (`f ++ `_unsafe_rec) = `f by decide]

/-! ### The mutual block: what `decl_run`'s relaxation buys, and what it costs (Γ-W5)

The fixture is the two-declaration twin of `rec_exit_registers_name`'s: a block whose
`ci.all` is `[f._unsafe_rec, g._unsafe_rec]` — the `._unsafe_rec` shape slice Γ-W0 measured
`getDeclInfo?` to answer with, at the arity the old field forbade. Three things are checked
on it: that the relaxed conjuncts hold, that the *old* conjunct is refuted, and that the
run's own `single_decl` test sends this block down the branch step 6 now walks. -/

/-- The block's names, as `getDeclInfo?` hands them back: two siblings, both suffixed. -/
def gMutualNames : List Name := [`f ++ `_unsafe_rec, `g ++ `_unsafe_rec]

/-- The fragment that contains them, keyed the way `decl_run` reads them — at the
*stripped* names, which is what the caller asks for and what the exit registers under. -/
def knownMutual : Name → Prop := fun n => n = `f ∨ n = `g

/-- **The relaxation is a relaxation.** The three conjuncts the field states since Γ-W5 are
*implied* by the pair it stated before (`ci.all = [m]`, `remove_unsafe_rec m = n`) together
with the field's own `known n` premise — so no producer that could satisfy the old field
fails the new one, and no consumer of the old field lost anything it was using. Step 6's
single-declaration arm reads them back exactly here. -/
theorem gDeclRunMutual_of_single {known : Name → Prop} {n m : Name} {ci : ConstantInfo}
    (hkn : known n) (hall : ci.all = [m]) (hstrip : remove_unsafe_rec m = n) :
    (∀ m' ∈ ci.all, known (remove_unsafe_rec m')) ∧
      (ci.all.map remove_unsafe_rec).Nodup ∧ n ∈ ci.all.map remove_unsafe_rec := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [hall]
  · intro m' hm'
    obtain rfl : m' = m := by simpa using hm'
    rw [hstrip]; exact hkn
  · simp
  · simp [hstrip]

/-- **…and it is not a cosmetic one: the old conjunct is *false* at a genuine mutual
block.** `ci.all = [m]` says the fetched declaration is alone in its block, which is
exactly what a two-member block is not. So the pair the field used to state was
unsatisfiable at every mutual declaration in a dependency cone, and no downstream work
could have repaired that — the same shape of finding as Γ-W2's, one level out. -/
theorem gDeclRunSingle_mutual_refuted : ¬ ∃ m : Name, gMutualNames = [m] := by
  rintro ⟨m, hm⟩
  simp [gMutualNames] at hm

/-- **The relaxed field is inhabited by a genuine two-member block**, and the block takes
the branch the slice walks.

Four checks, in the order step 6 consumes them: the fragment contains both siblings at
their stripped names; the stripped names are distinct (the `Nodup` `mkDef`'s fold and the
registration `forIn` both need, and which nothing in `ConstantInfo` supplies); *either*
sibling the caller asks for is among them; and the run's own test `ci.all.length == 1`
comes back **false**, so `visitMutual` skips the `@[inline]`/`value?`/`isExtern` prefix
entirely and `nonrecursive` — being `single_decl && …` — is `false` with it. That last
conjunct is why the multi-declaration arm of step 6 is the *shorter* path. -/
theorem gDeclRunMutual :
    (∀ m ∈ gMutualNames, knownMutual (remove_unsafe_rec m)) ∧
      (gMutualNames.map remove_unsafe_rec).Nodup ∧
      `f ∈ gMutualNames.map remove_unsafe_rec ∧
      `g ∈ gMutualNames.map remove_unsafe_rec ∧
      (gMutualNames.length == 1) = false := by
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · intro m hm
    simp only [gMutualNames, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact Or.inl (by decide)
    · exact Or.inr (by decide)
  · simp only [gMutualNames, List.map_cons, List.map_nil]
    rw [show remove_unsafe_rec (`f ++ `_unsafe_rec) = `f by decide,
      show remove_unsafe_rec (`g ++ `_unsafe_rec) = `g by decide]
    decide
  · simp only [gMutualNames, List.map_cons, List.map_nil]
    rw [show remove_unsafe_rec (`f ++ `_unsafe_rec) = `f by decide]
    simp
  · simp only [gMutualNames, List.map_cons, List.map_nil]
    rw [show remove_unsafe_rec (`g ++ `_unsafe_rec) = `g by decide]
    simp

/-- **The fetched block strips to the block `Γ` registers.** `getDeclInfo?` answers with
`._unsafe_rec` names and `visitMutual` registers under `names.map remove_unsafe_rec`; at
arity two this is where the two lists have to line up *in order*, since `Erases.fix`'s
`hreg` reads the `j`-th name against the `j`-th definition. `Erases.lean`'s `fixMutNames`
is that stripped list, and `ΓfixMut` registers along it. -/
theorem gMutualNames_stripped : gMutualNames.map remove_unsafe_rec = fixMutNames := by
  simp only [gMutualNames, fixMutNames, List.map_cons, List.map_nil]
  rw [show remove_unsafe_rec (`f ++ `_unsafe_rec) = `f by decide,
    show remove_unsafe_rec (`g ++ `_unsafe_rec) = `g by decide]

/-- **And the exit registers *both* siblings**, so motive 6's conclusion
`(s₁.constants.get? n).isSome` holds at whichever of the two the caller asked for — the
arity-2 twin of `rec_exit_registers_name`, on the same `._unsafe_rec` shape. Under the old
field only one of these two rows could ever be reached, because the block it admitted had
one row. -/
theorem gRecExitRegistersBoth (defs : List (@FixDef LBTerm)) :
    ((recConstState (gMutualNames.map remove_unsafe_rec) defs {}).constants.get? `f).isSome ∧
      ((recConstState (gMutualNames.map remove_unsafe_rec) defs {}).constants.get?
        `g).isSome := by
  simp only [gMutualNames, List.map_cons, List.map_nil]
  rw [show remove_unsafe_rec (`f ++ `_unsafe_rec) = `f by decide,
    show remove_unsafe_rec (`g ++ `_unsafe_rec) = `g by decide]
  refine ⟨?_, ?_⟩ <;>
    simp [recConstState, show ¬ (`g : Name) = `f by decide, show ¬ (`f : Name) = `g by decide]

/-- **`BlockHyps`' keying is load-bearing** (slice Γ-W2), on the measured data.

The block loop's `m` ranges over `ci.all`, which slice Γ-W0 measured to be `._unsafe_rec`
names for the declarations the fragment has to contain. The fragment itself holds the
plain names. So a field keyed on `known m` is uninhabited at exactly the sibling the loop
is looking at, while the same field keyed on `known (remove_unsafe_rec m)` fires — and the
difference is not cosmetic: keyed the wrong way the whole bundle would be *vacuously*
satisfiable and would supply nothing at the point of use.

Both halves are decided on the fixture's real shape, `f._unsafe_rec`. -/
theorem gBlockKeying :
    (fun n => n = `f) (remove_unsafe_rec (`f ++ `_unsafe_rec)) ∧
      ¬ (fun n => n = `f) (`f ++ `_unsafe_rec) :=
  ⟨by decide, by decide⟩

/-- **`BlockHyps` is satisfiable at a *non-empty* fragment** (slice Γ-W2) — the guard the
design asks to land in the same commit as the structure, so that the bundle is never a
shipped-then-refuted certificate.

The fragment is `{f}`, the ambient context is `Erases.lean`'s recursion fixture `ΓfixRec`
(which registers the one-def block for `f` and leaves `fixvars` at `⊥`), and `Esrc` records
`f`'s prepared body `fixRecSrc = fun (a : Prop) => f a`. What is *checked* here rather than
assumed is the one genuine scope field: `block_lam` has something to say at `f` — `Esrc`'s
entry really is λ-headed — so the field is not true merely because the fragment is empty.

The two run-keyed clauses stay hypothetical, for the same reason `BridgeHyps`' fields do:
they quantify over opaque runtime primitives. The two residues stay hypothetical because
that is what they are — `strengthen` is commissioned upstream and `nonest` is the standing
`instFixvars` residue, both premises of the cold-start capstones already
(`ColdStartDelta.gRecEnvConsistentD8` takes `hnest` in exactly this shape). -/
theorem gBlockHyps (env : VEnv) (Us : List Name) (cfg₀ : ErasureConfig)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (hlp : ∀ {m : Name} {ci : ConstantInfo} {s s' : ErasureState}
        {ctx : ErasureContext} {w w' : Void IO.RealWorld},
      (fun n => n = `f) (remove_unsafe_rec m) →
      (getConstInfo m : EraseM ConstantInfo) s ctx cctx ref w = .ok (ci, s') w' →
      ci.levelParams <+: Us)
    (hesrc : ∀ {m : Name} {ci : ConstantInfo} {pe : Expr}
        {sc s s₁ : ErasureState} {ctx ctx' : ErasureContext}
        {wc wc' w w₁ : Void IO.RealWorld},
      (fun n => n = `f) (remove_unsafe_rec m) →
      (getConstInfo m : EraseM ConstantInfo) sc ctx' cctx ref wc = .ok (ci, s) wc' →
      prepare_erasure (ci.value! (allowOpaque := true)) s ctx cctx ref w = .ok (pe, s₁) w₁ →
      ctx.config = cfg₀ →
      gEsrcδ fixRecSrc (remove_unsafe_rec m) = some pe)
    (hstr : ErasableStrengthen env Us)
    (hnest : ∀ {fv : Name → Option FVarId} {Δ' : VLCtx} {n' : Name} {ty' b' : Expr}
        {bi' : BinderInfo} {d' : List (@FixDef LBTerm)} {i' : Nat},
      Erases env Us (ΓfixRec.withFixvars fv) Δ' (.lam n' ty' b' bi') (.fix d' i') →
      Erases env Us ΓfixRec Δ' (.lam n' ty' b' bi') (.fix d' i')) :
    BlockHyps env Us (fun n => n = `f) ΓfixRec cfg₀ (gEsrcδ fixRecSrc) cctx ref where
  block_lparams := hlp
  block_esrc := hesrc
  block_lam := by
    rintro m pe rfl hb
    obtain rfl : pe = fixRecSrc := (by simpa using hb : fixRecSrc = pe).symm
    exact ⟨by simp [NoProj, fixRecSrc],
      `a, .sort .zero, .app (.const `f []) (.bvar 0), .default, rfl⟩
  strengthen := hstr
  nonest := hnest

/-- **…and the field it checks is not vacuous**: the fragment really contains `f`, `Esrc`
really records a body for it, and that body really is a projection-free λ. Read together
with `gBlockKeying` this is the whole non-vacuity story for the scope half of
`BlockHyps`. -/
theorem gBlockLam_nonvacuous :
    (fun n => n = `f) `f ∧ gEsrcδ fixRecSrc `f = some fixRecSrc ∧ NoProj fixRecSrc ∧
      ∃ n ty b bi, fixRecSrc = Expr.lam n ty b bi :=
  ⟨rfl, by simp, by simp [NoProj, fixRecSrc],
    `a, .sort .zero, .app (.const `f []) (.bvar 0), .default, rfl⟩

/-- **The fragment's constant is `Supported`** — the derivation that was unreachable at
`known = ⊥` (`Supported.const` needs `known n`, and `Γ.fixvars = ⊥` kills the other
disjunct). This is what δ-inclusion is *for*. -/
theorem gDeltaSupported : Supported (fun n => n = `f) gΓδ (.const `f []) :=
  .const `f [] (Or.inl rfl) rfl rfl

/-! ### The universe scope: what the prefix pin buys, and what it does not (slice Γ-U2)

`decl_run`'s last conjunct, `BlockHyps.block_lparams`, `BridgeInv.lparams` and
`BridgeHyps.orc_run`'s scope guard all read `<+: Us` since Γ-U2, where they read `= Us`.
The plan of record (the Γ-U analysis above) warned that a Γ-U2 shipping alone would be a
legibility regression *if* it traded a named restriction for vacuity. The five checks
below are the machine-checked reason it does not, and they are also the honest statement
of the slice's reach: it widens the **subject** side, not the dependency side. -/

/-- **At a closed subject the prefix pin *is* the old pin.** Every capstone in this
development runs at `Us = []`, and there `Lp <+: []` holds exactly when `Lp = []` — the
universe monomorphism the field demanded before. So no shipped instantiation weakened, no
producer's obligation got easier, and no field became vacuous: at the configuration the
development actually uses, Γ-U2 is a *no-op*, which is the answer to "does it trade a
restriction for vacuity". -/
theorem gPrefixPin_closed_subject (Lp : List Name) : Lp <+: ([] : List Name) ↔ Lp = [] :=
  List.prefix_nil

/-- **…and at a polymorphic subject it genuinely widens.** At `Us = [u]` the old pin
admitted exactly the dependencies declared `.{u}`; the prefix pin admits those *and* every
monomorphic one — which is the common shape, a `{u}`-polymorphic function calling
`Nat.add`. Nothing about this case was reachable before: the old field was false at it. -/
theorem gPrefixPin_widens :
    ([] : List Name) <+: [`u] ∧ ¬ ([] : List Name) = [`u] ∧ ([`u] : List Name) <+: [`u] :=
  ⟨List.nil_prefix, by simp, List.prefix_refl _⟩

/-- **What it does not buy: a polymorphic dependency of a closed subject.**
`OfNat.ofNat` is `.{u}` and the capstones are at `Us = []`, so `[u] <+: []` is false and
its declaration stays outside the fragment, exactly where it was before Γ-U2. That case
needs *instantiation*, not weakening — it is what Γ-U3/Γ-U4 owe — and it is why this
slice's ledger claim reads "polymorphic subjects with prefix-scoped dependencies" and not
"polymorphic dependencies". -/
theorem gPrefixPin_no_polymorphic_dep : ¬ ([`u] : List Name) <+: [] := by simp

/-- **The two fields finding (b) named do not have to move** — and this is where the Γ-U1
kit is consumed.

`prepared` and `esrc_shape` state translatability at the **ambient** `Us`, and the Γ-U
analysis read that as "relaxing `decl_run` alone is a no-op, because two more fields pin
the same restriction". Under the *prefix* reading that conclusion is wrong, and this is
the correction: a producer proves the natural fact at the dependency's own scope `Lp`, and
`TrExprS.prefix_weaken` carries it to `Us` on the nose — same source, same `VExpr`, no
`≈` residue. So the ambient-`Us` fields are *implied* by their own-scope forms and only
the four scope pins had to move. (Finding (b) stays correct as stated, about the
*instantiation* reading it was written for: there the transport is `TrExprS.instL`, which
lands in `TrExpr`, and nothing carries a strict witness across.) -/
theorem gPreparedAtPrefix {env : VEnv} {Lp Us : List Name} (hp : Lp <+: Us) {pe : Expr}
    (h : ∀ Δ : VLCtx, ∃ ve, TrExprS env Lp Δ pe ve) :
    ∀ Δ : VLCtx, ∃ ve, TrExprS env Us Δ pe ve :=
  fun Δ => (h Δ).imp fun _ => TrExprS.prefix_weaken hp

/-- **…while at a closed subject a polymorphic body is refuted outright, not merely
unproven.** `esrc_shape` demands `TrExprS env Us [] pe ve`, and at `Us = []` there is no
such derivation for a body mentioning `u`: `VLevel.ofLevel` resolves a parameter by its
*position* in the scope, and the empty scope has none. This is the sharp form of "the
prefix cannot reach the typeclass layer" — the obstruction is in the relation, one
constructor deep, and no bundle-side relaxation can move it. -/
theorem gEsrcShape_polymorphic_dep_refuted (env : VEnv) :
    ¬ ∃ ve, TrExprS env [] [] (.sort (.param `u)) ve := by
  rintro ⟨ve, h⟩
  cases h with | sort h => simp [VLevel.ofLevel] at h

/-- **The dependency's erasure lands in the subject's scope.** What makes the relaxed pins
usable rather than merely stateable: a body erased at the reader `visitMutual` installs
for a monomorphic dependency (`Lp = []`) is an `Erases` derivation at the polymorphic
ambient scope `Us = [u]` the bridge's conclusion is stated at — same source, same target,
no side condition (`ErasesLevels.Erases.prefix_weaken`, through the `lam` arm, which is
one of the three that carry a strict `TrExprS`). Built at an arbitrary `env`/`Γ`, so what
it checks is the scope and nothing else. -/
theorem gErasesDepPrefix (env : VEnv) (Γ : ErasureCtx) (nm : Name) (bi : BinderInfo) :
    Erases env [`u] Γ [] (.lam nm (.sort .zero) (.bvar 0) bi)
      (.lambda (nameToBinder nm) (.bvar 0)) :=
  Erases.prefix_weaken List.nil_prefix
    (.lam (ty' := .sort .zero) (.sort rfl) (.bvar 0))

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
