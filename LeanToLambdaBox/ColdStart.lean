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
| `NoBlock t` (applied form of the output) | `visitExpr_noBlock` (R11's third conjunct, no hypotheses — slice δ-N) |
| `NoBlockEnv sf.gdecls` (applied form of every recorded body) | `visitExpr_noBlockEnv` (δ-N: `NoBlockEnv` is a `RunClosed` predicate) |
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
* Both residues this slice used to name are **gone**: applied form at δ-N, and
  context-uniformity at δ-D7a/δ-D7b. See the residue list below for what replaced them.

`SEnvConsistent` is **not** derived and should not be: it says the prepared body is defeq
to the kernel's value for the constant, which is a `PrepareHyps`-class fact about the
elaborator, not about the walk. The δ guard at the end of this file discharges it at a
concrete two-declaration environment, from `VEnv`'s own defining equation.

## THE TRUST LEDGER — every premise of the two cold-start capstones, classified

This is the definitive classification for `shipping_erase_correct_firstorder_coldstart`
and its ι twin; the ι rows are marked, everything else is common to both. Read it with
`FirstOrderShippingIota.lean`'s D3ι ledger, which classifies the ι block in more detail.
Four classes, and nothing falls outside them:

* **C — proved-guard-backed certificate.** `rfl`/`decide`-checkable data about a concrete
  `Γ`/`env`, *constructed* in the guards at the end of this file. No run, no opaque
  primitive, no trust.
* **H — runtime Hoare bundle.** A spec for one *real* call on the erasure's path. Never
  an axiom; its global satisfiability is not in-logic decidable because the primitive is
  an opaque `ST`/`EIO` operation. This is the documented trust boundary, the same one
  `BridgeHyps` has carried since the bridge landed.
* **S — scope restriction.** Narrows the class of programs the statement speaks about. A
  violation makes the *premise* unsatisfiable; it never makes the theorem false.
* **R — residue.** Believed, named, not proved. **One** of it, listed after the table —
  down from three at the previous slice.

| premise | class | note |
|---|---|---|
| `hrun : Erasure.erase e cfg … = .ok (p, inls) w'` | — | the subject. No run of the family is constructible in-logic (opaque `CoreM`/`MetaM` primitives, a real `ST.Ref`), so it stays hypothetical in every guard |
| `henv : env.WF` | C | `envFO_wf` / `envδ_wf`, built from lean4lean's own `VDecl.WF` |
| `hUs : Us = []` | S | universe monomorphism of the whole dependency cone. At the *entry point* it is also a fact — `Erasure.run` installs `lparams := []` and `BridgeInv.lparams` pins `ctx.lparams = Us` — but `DeltaHyps.decl_run` demands it of every dependency too, so a polymorphic callee makes the bundle uninhabited (`DeltaHyps`, scope restriction 1) |
| `hcsimp : cfg.csimp = false` | S | csimp replacement is not kernel-semantics-preserving (`PrepareHyps`' own analysis), so it can never sit inside a correctness statement. It is also what makes R2 fire (`ColdStartRun.run_prepare_erasure_state`: with csimp off, `prepare_erasure` leaves the state at `{}`). RAISE-not-fix: the shipping *default* is `csimp := true` |
| `hnfv : Γ.fixvars = ⊥` | S | the subject is outside every mutual block. Also `DeltaHyps.nofixvars` (scope restriction 2) |
| `hnorec : Γ.recBodies = ⊥` | S | **no recursive dependency at a cold start.** Feeds `recEnvConsistent_of_noRec`. The recursion machinery (W0–W3.1) is *live* in the warm theorems, and since δ-D8 the walk fact behind `RegisteredClosureRec` is a theorem too (`ColdStartDelta.recEnvConsistent_of_block`). What keeps this row here is that no *run* reaches those theorems: `DeltaHyps.nonrecursive` (δ-D8e, split out of `decl_run`) forces `visitMutual`'s `nonrecursive` test `true` for every fragment name, so the bridge's step 6 refutes the recursive exit. Removing that field is necessary and **not sufficient** — see residue 1 and `VisitExprRefines.bridgeInv_blockReader_refuted` |
| `hnat : Γ.natPeano → cfg.nat = .peano` | C | `by simp [Γ…]`; pins the run's config against `Γ`, which is what `Supported.natLit` cashes in |
| `Hr : RegBridgeHyps Γ` | H, and `knames` is C | after S1e it carries only: the naming convention (C), the `Γ`-agreement for a *cold* `register_inductive` (H — the cold branch reads the environment, so no run of it is constructible; the *hit* branch is, which is why the guard is load-bearing: `regShapeHyps_regCtors_refuted`), registration completeness, and the `prepare_erasure` trust item. Registry-invariant preservation is **no longer here** — it is the theorem `ColdStartInduction.visitExpr_regInvShape` |
| `hcon : SEnvConsistent env Us Esrc` | H (`PrepareHyps` class), C at the δ guard | "the prepared body is defeq to the kernel's value for the constant" — a fact about the *elaborator*, not about the walk, so it is deliberately not derived. Discharged at `envδ` from `VEnv`'s own defining equation (`envδ_senvConsistent`), the first non-vacuous instance in this development |
| `H : BridgeHyps` / `HD : DataBridgeHyps` / `C : CasesBridgeHyps` | H | the three original bundles, unchanged |
| `Hδ : DeltaHyps` | H + S | mixed by field, and deliberately: the five `…_run` clauses are H (generator bookkeeping for the `visitMutual`-only primitives); `esrc_sub`/`disj`/`kinj`/`nofixvars`/`decl_run`/`nonrecursive`/`prepared`/`prep_esrc`/`axiom_free`/`esrc_shape` are S (the fragment's own closure conditions). The `uniform` field is **gone** (δ-D7b) — context-uniformity is now a theorem; `nofixvars` is **conditioned on the fragment** (δ-D8), which is what makes the bundle inhabitable at a block-local `Γ.withFixvars fv` and costs nothing at a top-level one; and the recursion exclusion is **its own field** since δ-D8e (`nonrecursive`), because it is a restriction on the fragment and not a fact about the declaration fetch, and because it is the one field `hnorec` is waiting on |
| `S : ColdStartSubject` | S | one field left. `supported` — the prepared term is in the fragment and lean4lean-translatable, the same premise `DeltaHyps.prepared` makes for the callees. `noBlock`/`noBlockEnv` retired at δ-N |
| `hev : SEvalData{C,ι} … (Esrc.walked Γ sf.gdecls) pe v` | S | the source evaluation, stated about `prepare_erasure e` (what the run erases) and at the walk-restricted environment (what the run registered) |
| `hfo : FirstOrderValue env Us Γ [] v` | S, C at the guards | first-order *result*. Constructed at every guard modulo `harity`, the one lean4lean-blocked side condition `FirstOrder.lean` documents |
| `hiota : IotaConsistent` (ι) | H | the interface premise; `…ι_of_shape` discharges it from `PatsIotaSpec + SEnvConsistent + IotaShape`, at eight further lean4lean *modelling* axioms and no axiom of ours |
| `hrel : IotaRelevant` (ι) | S | excludes `Erases` derivations that box a proper prefix of an ι redex; the shipping `visitCases` emits none |
| `hiacoh : IotaArityCoherent` (ι) | C | `ΓFOι_iotaArityCoherent` |
| `hcc` (ctor/`casesOn` disjointness) | C | `ΓFOι_cc` |
| `hstr : ErasableStrengthen env Us` | **R** | the only one left. A three-line `VExpr`-level statement — `HasType.weakN_inv` for the shipping `VEnv.HasType`. Commissioned upstream as C1 and **NOT discharged** by the trproj round; a written analysis came back instead, and it argues the route is blocked. See residue 2 below |

**Derived from the run, and therefore absent from the list above** — the `ErasureState`,
the environment `E`, `ClosedEnv E`, `LBClosed t 0`, the bridge invariant, the three
registration records, `ErasesEnvDeltaData`, `RecEnvConsistent`, the `Program` shape, and
(since S1e) the registry invariant's preservation. `PrepareHyps.prepare_sound` is derived
too: it is the theorem `ColdStartRun.prepare_sound_of_prepareHyps`, so that bundle is down
to three fields. `ColdStartInduction.RegShapeHyps` is **not used at all** — it is refuted
below, three ways.

**The residues: one, and who owes it.**

0. **How to read this list.** The repo keeps a refuted or retired item next to its record
   rather than deleting it, so the three entries below are the three the previous slice
   named. Only **one** is still a residue, and only one is a capstone premise of class R:
   `hstr : ErasableStrengthen env Us`, inside entry 2.

1. ~~`EnvErasureRec.RegisteredClosureRec`~~ — the δ witness for a *recursive* block.
   **DEMOTED, slice δ-D8**, and never a capstone premise: `hnorec` (S) stood in for it, so
   it always cost scope rather than trust.

   Slice D6 walked the recursive exit's `List.mapM` and supplied most of
   `erases_fix_of_open`'s premise list from the run. What was left was `hopen` at the
   block-local `Γ.withFixvars fv` — filed as "the `Γ`-inside-the-motives generalisation",
   design §W3.2/D8 — and `hreg`. The first turned out **not to need any motive change**:
   `visitExpr_refines_erases` binds `Γ` as a plain implicit and `VisitExprRefines` declares
   no `variable`, so it is Γ-polymorphic *as a statement*, and of its premises exactly one
   breaks at a block-local `Γ`: `DeltaHyps.nofixvars`, which asserted `Γ.fixvars = ⊥`
   unconditionally and is now conditioned on the fragment — the only thing its two
   consumption sites ever had in scope. Hence
   `VisitExprRefines.visitExpr_refines_erases_block`,
   `RecBlockErasure.erases_rec_block_of_run` and
   `ColdStartDelta.recEnvConsistent_of_block`: the record's `erase` field is now *derived*.

   What survives is not an `Erases` certificate but a **registration agreement** — "the `Γ`
   you supply names *this* block, under the map the run installed" (`hreg`/`hfv`/`hcov`) —
   irreducible at a parameter `Γ`, which is fixed before the run builds `defs`, and of the
   same class as `BridgeInv.knames`; plus `hnd` (freshness, `BridgeHyps.fresh_run`'s
   business) and the standing `hnest` residue of `Erases.instFixvars`. The price is a named
   scope restriction: **a block's bodies call only its own siblings, registered
   constructors and registered `casesOn`s** — the block's inner runs are taken at
   `known = ⊥`, so an external call is out of scope.

   **`hnorec` does not trade for this, and slice δ-D8e found out why** — correcting what
   the previous slice recorded here.

   The *proximate* gate is a premise, and it now has a name of its own:
   `DeltaHyps.nonrecursive` demands `name_occurs n v = false` of every fragment name, which
   forces `visitMutual`'s `nonrecursive` test `true`, so the bridge's step 6 *refutes* the
   recursive exit rather than walking it. δ-D8e split that clause out of `decl_run` — it is
   a restriction on the fragment, not a fact about the fetch — so the trade is a one-field
   trade rather than surgery on a five-conjunct spec.

   The previous slice's plan for the rest — "the `δ` transport across `recConstState`
   composes, plus the block loop's generator bookkeeping, plus the `remove_unsafe_rec`
   scope restriction" — is **incomplete, and the missing item is structural.** Removing
   `nonrecursive` lets the run *reach* the recursive exit; it does not let the bridge
   *walk* it. Inside `visitExpr_refines_erases_core` the exit's per-sibling erasures are
   runs of the induction's **abstract** fixpoint argument, so the only thing available
   about them is the motives — and the motives fix one `Γ`. The exit runs each sibling
   under the reader carrying the block's fixvar map, while `BridgeInv.fixvars` is an *iff*
   against `Γ.fixvars`, which `DeltaHyps.nofixvars` pins at `⊥` for a fragment name. The
   erasure IH's own premise is therefore **false** at that reader:
   `VisitExprRefines.bridgeInv_blockReader_refuted`, with the instance at the block reader
   itself, `bridgeInv_rec_exit_reader_refuted`.

   So the `Γ`-inside-the-motives generalisation, which δ-D8 correctly reported was
   unnecessary for the bridge theorem *as a statement*, is still necessary *inside* the
   induction, and it is what this row is really waiting on. Concretely, in order:
   quantify `(known, Γ, Esrc)` and the four trust bundles inside all eighteen motives (≈40
   IH application sites, ≈30 bundle uses); a `List.mapM` decomposition for the block loop
   that **chains** states and worlds — `ColdStartRun.run_rec_exit_siblings` is
   deliberately `gw`-free and hands its per-sibling runs back at unrelated states, which is
   exactly what a `BridgeInv` cannot be rebuilt from; the transport of the *outer* δ record
   across the block's inner runs (they register no constant body, but nothing states that
   yet); the block-local `Supported`/`TrExprS`/`Esrc` premises for the sibling bodies,
   which the `known = ⊥` bundle cannot supply because every one of its scope fields is
   keyed on `known n`; and the `remove_unsafe_rec` scope restriction, which is real —
   `DeltaHyps.rec_exit_registers_stripped_name` shows motive 6's conclusion is *false*, not
   merely unproved, at an `._unsafe_rec` name. `ColdStartDelta`'s recursion section carries
   the premise-by-premise ledger for everything downstream of that.

   **Status of that list after slices Γ-W0/W1/W2** — five landed, one narrowed, one
   dissolved, one found. The generalisation is **narrower** than priced: only `Γ` moved, as
   a bound variable plus a one-equation coherence hypothesis, and `known`, `Esrc` and all
   four bundles stayed outer (Γ-W1; 34 signature edits, 33 IH sites, 0 admissibility
   edits). The chaining loop rule is `Erasure.run_rec_exit_siblings_chained`, and the fresh
   ids come back `Nodup` from `Erasure.run_mkFreshFVarId_list` (Γ-W0). The outer δ record's
   transport **dissolved**: indexing `RunConclδ` at the ambient `Γ₀` rather than at the
   motive-local `Γ` means the inner runs are *allowed* to register things and the record
   carries them (Γ-W1); `DeltaMem.recBlock`/`RunConclδ.recBlock` are the extension step.
   The block-local scope premises are `DeltaHyps.BlockHyps` (Γ-W2), five fields rather than
   the seven priced — and keyed on `known (remove_unsafe_rec m)`, because the loop's `m`
   ranges over `ci.all`. The `remove_unsafe_rec` restriction was **not** real in the
   direction recorded above: the suffix rides on the *fetched* declaration, not on the
   caller's name, so the repair was to relax `decl_run` to `ci.all = [m] ∧
   remove_unsafe_rec m = n` (Γ-W2a) — after which the fragment *gains* the arithmetic the
   §H benchmarks need, which is the opposite of a restriction. And one item the list did
   not have at all: the four block results lived **downstream** of `VisitExprRefines`, so
   step 6 could not call them; Γ-W2 moved their cone into `RecBlockErasure.lean`, verbatim,
   below the bridge. What is left is the branch itself.

   The capstone half cannot be landed ahead of that producer either, and for a reason that
   is not effort: it would replace a named scope restriction with an *uninhabited* premise.
   See the section "The `hnorec` trade, and why its capstone half cannot be landed first"
   below, and `nonrec_exit_stores_no_fix`.

   Slice `rec` repaired the theorem this entry is about. `erases_fix_of_open`'s `hopen`
   quantified over *every* `Δf`, and in that form it is **unsatisfiable for every
   self-referential block** — `Erases.fixvar` is the only rule taking a `.const` source to
   an `.fvar` target, and its `hfresh` is anti-monotone in `Δ`. It had no non-vacuity
   guard, which was the tell: the file's own fixture carries exactly the missing side
   condition and so could never feed it. `hopen` is now conditioned on a fresh `Δf`,
   `Erases.fix`'s unrestricted `hbodies` is rebuilt through `[]` with `erases_weak_any`,
   and `gErases_fix_of_open` is the guard it never had. Slice δ-D8 finished the job: the
   proof instantiates `hopen` at `Δf := []` and nowhere else, so `erases_fix_of_open_nil`
   states it there — a strictly weaker premise, and the only one a *run* can supply.
2. `DeltaHyps.uniform` — context-uniformity (`∀ Δ`) of a constant body's erasure. The
   bridge fires at the `Δ` of the call site, and `RegisteredClosure*.erase` needs every
   `Δ`.

   **The blame was misplaced** (slice δ-D7a). This row used to say the gap was "a
   lean4lean-side `TrExprS`-weakening obligation"; `TrExprS.weakFV`
   (`Verify/Typing/Lemmas.lean:596`) has been proved upstream all along. The
   **weakening** half is now a theorem of this development with no residue at all:
   `ErasesStrengthen.erases_weakFV` (along a `VLCtx.FVLift`) and
   `ErasesStrengthen.erases_weak_any` (out of `[]` into *every* `VLCtx`, for a closed,
   fvar-free source and a closed target — the shape `Erases.fix`'s unrestricted `∀ Δf`
   demands). Two corrections fell out of proving them, both recorded at the lemmas:
   lean4lean's `weakFV` asks for `VLCtx.WF` of the target context, which the `lam`/`letE`
   cases cannot re-establish (`Erases.lam` carries no `IsType` for its binder type) and
   which is more than the proof consumes — `VLCtx.FVWF` suffices and conses freely; and
   at an unrestricted `Δ` even `FVWF` is unavailable, where fvar-*freeness* of the source
   removes the hypothesis outright, since no `.inr` lookup ever happens.

   What is left is the **other** direction, `Δ → []`, and it is not about `Erases` or
   about `TrExprS` either: it is `Erasable`/`HasType` **strengthening**, the inverse of
   `weakN`. lean4lean has `HasType.weakN_inv` for the *stratified* theories only; the
   shipping `VEnv.HasType` used by `Verify/Typing` has no such lemma. That is the whole
   of residue 2, stated at the `VExpr` level — which makes it a contribution to lean4lean
   rather than a debt of this development. The `Δ` the record starts from now travels
   with its own well-formedness and `NoBV` (slice δ-D7b(i), `DeltaMem`), so nothing else
   stands between the premise and its discharge.

   **Discharged** (slice δ-D7b). `ErasesUniform.erases_strengthen_closed` does the
   `Δ → []` direction and `erases_uniform_closed` composes the two, so the field is
   deleted from `DeltaHyps` and the capstones call the theorem. What is left is the
   premise `hstr : ErasableStrengthen env Us`, a three-line statement at the `VExpr`
   level and the only R-class row in the table above. Two things the bundle owes it are
   S-class and now written down: `DeltaHyps.esrc_shape` (a fragment body is
   projection-free and translates at `[]` — `NoProj` is what makes lean4lean's
   `TrExprS.unique`, which is `sorry`-free, applicable, and the supported fragment
   excludes `.proj` anyway), and the context data `DeltaMem` now carries (δ-D7b(i)).

   Honest note on the upstream side, established while proving this: lean4lean does
   **not** have `HasType.weakN_inv` even for the stratified theories — those statements
   sit inside comment blocks whose supporting `IsDefEq.weakN_inv` has `sorry` arms — and
   for the shipping `VEnv.HasType` the corresponding `IsDefEqU.weakN_iff`
   (`Theory/Typing/UniqueTyping.lean`) is itself a `sorry`. So discharging `hstr` from
   what upstream has today would import a gap rather than close one. Naming it keeps the
   gap where a reader can see it.

   **Asked for upstream, and answered — in the negative (2026-08-27, pin `fee3ada`).**
   This was commission item C1. It did not close, and the round delivered the sanctioned
   alternative: a written analysis of *where* it breaks, which is a better result than a
   reshaped `sorry`. The line `UniqueTyping.lean:174` is byte-identical to the ι head —
   no new statement, no renamed gap, no freshly-sorried `HasType.weakN_inv` exported for
   us to consume. The analysis:

   * strengthening inducts on the `IsDefEq` derivation and every structural case goes
     through, `defeqDF` included (`IsDefEqU` discards the type);
   * `trans` is the irreducible obstruction — the middle term of a conversion chain is an
     arbitrary `VExpr`, not a lift, so neither IH applies;
   * eliminating `trans`-intermediates is what confluence buys, and the confluence route
     is blocked **two independent ways**: a module import cycle (`ChurchRosser.lean`
     *imports* `UniqueTyping.lean`, so `weakN_iff` sits structurally upstream of all
     reduction machinery), and a same-measure logical cycle (`weakN_iff` is called
     non-reflexively at the same size from the confluence development itself, with no
     evident well-founded measure — `Prop`-impredicativity and `imax` defeat level
     measures);
   * and the sharpest finding, which we had not predicted: closing the `church_rosser`
     `pat` `IOTA-TODO` would be **necessary but not sufficient**. Landing ι-confluence
     does not unblock C1.

   So `hstr` **stays a named premise**, and this row stays class R. That is the standing
   recommendation from both sides now, not an assumption of ours. The complementary
   observation is that its cost stopped growing: the `Δ → []` half is a theorem here, and
   since `TrProj` got a real definition (pin `fee3ada`) nothing else in this ledger
   inherits anything from the projection cluster.
3. ~~`ColdStartSubject.noBlock` / `noBlockEnv`~~ — **RETIRED, slice δ-N.** The stated
   obstruction ("not carryable by the shape induction") was a misdiagnosis, and the
   refutation is one line of the definition: `NoBlock` (`ErasesCorrectData.lean`) is
   `True` on `.box` — boxing is *invisible* to it — and `False` on exactly one node,
   `.construct _ _ (_ :: _)`. The eraser has exactly one `.construct` construction site
   (`Erasure.visitConstructor`), and it is **nullary by explicit design**: "in the stage
   of λbox I am targeting constructor application is function application". So `NoBlock`
   is true of every `visitExpr` output for a structural reason, and the shape induction
   carries it as `ShapeC`'s third conjunct alongside `NoFix`/`LBClosed`
   (`visitExpr_shape_all`). At the environment level `NoBlockEnv` is a `RunClosed`
   predicate (`ColdStartDelta.runClosed_noBlockEnv`): `inl` leaves `gdecls` alone,
   `addAxiom` conses a value-less entry, `register_inductive` conses an `.inductiveDecl`
   over a `ConstExt` prefix of value-less entries, and the two constant conses are handed
   the body's `NoBlock` by the widened `RunClosed.nrc`/`rc`. Only the standing
   `prepare_erasure` transparency item is assumed, and `DeltaHyps.prep_run` already
   states it. `ColdStartSubject` is down to a single field.

Nothing in this ledger is an axiom of ours. The measured axiom sets of both capstones are
`shipping_erase_correct_firstorder`'s **verbatim** — the three standard Lean axioms plus
`sorryAx` and the four `Lean.Expr`/`PersistentHashMap` modelling axioms, all inherited
through lean4lean.

## THE INHERITED BOUNDARY — what `sorryAx` means here (re-measured 2026-08-27, `fee3ada`)

The pin moved from the ι head `1a1ebe8` to `fee3ada`, head of the fork's `trproj` branch,
where **`TrProj` stops being a `sorry`**. That single change is worth stating precisely,
because for a year the honest answer to "what does the `sorryAx` in these capstones stand
for?" was partly wrong.

**What it never was.** `TrProj` used to be a `sorry`-valued *definition*, so `sorryAx`
entered through the **type** of `TrExprS` — every statement mentioning `Erases` or
`TrExprS` carried it whether or not its proof touched a projection. `#print axioms
Lean4Lean.TrProj` now reads `[propext]`, and with that channel closed **111 declarations
in `scratch/final_audit.lean` lost `sorryAx` outright**, entries carrying it going 230 →
91. Chief among them: `visitExpr_refines_erases` — the claim that the shipping eraser
refines this development's `Erases` relation — is now **sorryAx-free**, as are
`BridgeInv` and all its transports, `DeltaHyps`, `DeltaMem`, `RunConclδ`,
`ColdStartSubject`, `RecEnvConsistent`, the whole δ registration chain, and every
`Erases` transport and inversion lemma. The *refinement* half of this development inherits
nothing but modelling axioms.

**What it actually is, and what the capstones still pay.** Their set is verbatim
unchanged, and the `sorryAx` in it is **unique typing**, not projections:

* `Lean4Lean.TrExprS.uniq` → `Lean4Lean.TrProj.uniq`, still `PROJ-TODO`. 69 call sites of
  `.uniq` downstream — 31 in `ErasesCorrectData.lean`, then `ErasesCorrect.lean` (11),
  `ErasesCorrectIota.lean` (7), `ErasesUniform.lean` (4), `FirstOrder.lean` (2),
  `ErasesStrengthen.lean` (2), `SubjectReductionFull.lean` (1). The densest single line of
  inherited debt we carry.
* `Lean4Lean.VEnv.IsDefEq.uniqU`, sorried through `IsDefEqU.weakN_iff` (= C1, see residue
  2) and through the ι fork's `pat` cases. It reaches us via `TrProj.defeqDFC`,
  `TrExpr.app`/`TrExpr.proj` and `TrExprS.instL`.
* `Lean4Lean.VEnv.HasType.app_inv` (`Theory/Typing/Strong.lean`) — the ι spine
  construction.
* `Lean4Lean.Aligned.addInduct` — the ι fork's environment-alignment `IOTA-TODO`.

**The remaining upstream projection items — the PROJ-TODO trio.** Three, and only one has
downstream reach:

| item | upstream site | reaches us? |
|---|---|---|
| `TrProj.uniq` | `Verify/Typing/Lemmas.lean` | **YES**, through `TrExprS.uniq` (above). Blocked on the `Injectivity.lean` cluster, never in scope for the trproj round |
| `TrProj.weak'_inv` | `Verify/Typing/Lemmas.lean` | **no** — nothing here calls `TrExprS.weakFV'_inv`/`weakFV_inv`. `ErasesUniform.lean` deliberately routed around it, and that decision pays off twice: it dodged the A0 churn *and* this gap. Blocked on C1 |
| `TrEnv.proj_defeq` | `Verify/Environment/Lemmas.lean` | **not yet** — a real statement with a deferred proof (A2). A new interface, deliberately not consumed. Building on it is a design call for the next slice, not something to do because it type-checks |

**And what the merge cost.** `trproj` is a merge of upstream `master`, so this pin also
absorbs master's level-normalization rewrite, the K-target flag fix and
`lazyDeltaProjReduction` — about 5,200 lines of change nobody here commissioned. Two
axioms enter the audited surface with it: `Std.TreeMap.all_eq_all_toList`, a genuinely new
`axiom` in lean4lean's `Verify/Axioms.lean` (standing in for a `Std` lemma Lean does not
prove yet, leanprover/lean4#12798), and `Lean.Level.isExplicitSubsumedAux_eq`, declared
upstream already but unreached until now. Both land on the **executable kernel-checker**
cluster only — `TypeChecker.kernel_isErasable_sound`, `ResidualHyps.toBridgeHyps`,
`shipping_visitExpr_correct'` — and neither touches the capstones or the ι `_of_shape`
cluster. The commissioned commits themselves add no `axiom`.
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
    -- the sole surviving residue: one commissioned VExpr-level obligation (slice δ-D7b)
    (hstr : ErasableStrengthen env Us)
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
  -- δ-N: `prepare_erasure` leaves `gdecls` alone — `DeltaHyps.prep_run`'s state
  -- transparency, which is the one assumed slot of `runClosed_noBlockEnv`.
  have hprepg : ∀ {e' : Expr} {s : ErasureState} {ctx : ErasureContext}
      {cc : Core.Context} {rf : ST.Ref IO.RealWorld Core.State} {w₀ : Void IO.RealWorld}
      {pe : Expr} {s' : ErasureState} {w₁ : Void IO.RealWorld},
      Erasure.prepare_erasure e' s ctx cc rf w₀ = .ok (pe, s') w₁ → s'.gdecls = s.gdecls :=
    fun h => congrArg ErasureState.gdecls ((Hδ _ _).prep_run h).2
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
  -- context-uniformity (now the theorem `erases_uniform_closed`, modulo `hstr`) and
  -- applied form (now the theorem `visitExpr_noBlockEnv`).
  have hdelta : ErasesEnvDeltaData env [] Γ (Esrc.walked Γ sf.gdecls) sf.gdecls :=
    erasesEnvDeltaData_of_registeredClosureData
      (registeredClosureData_of_deltaMem_walked hmem
        (fun hb => (Hδ cctx ref).disj ((Hδ cctx ref).esrc_sub (by rw [hb]; simp)))
        hshape.closed
        (fun hb _ hlb hwf hnobv her =>
          -- Context-uniformity, DISCHARGED (δ-D7b): strengthen to `[]` through the one
          -- named obligation, then re-widen to *every* context with `erases_weak_any`.
          erases_uniform_closed henv hnfv hstr (VLCtx.FVLift.from_nil hnobv) hwf
            ((Hδ cctx ref).esrc_shape hb).1
            ((Hδ cctx ref).esrc_shape hb).2.choose_spec hlb her _)
        (visitExpr_noBlockEnv hprepg hvis noBlockEnv_empty))
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
      hvis hinv hsup htr (visitExpr_noBlock hvis) hcl (hev hpr hvis) hfo
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
    -- the sole surviving residue: one commissioned VExpr-level obligation (slice δ-D7b)
    (hstr : ErasableStrengthen env Us)
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
  have hprepg : ∀ {e' : Expr} {s : ErasureState} {ctx : ErasureContext}
      {cc : Core.Context} {rf : ST.Ref IO.RealWorld Core.State} {w₀ : Void IO.RealWorld}
      {pe : Expr} {s' : ErasureState} {w₁ : Void IO.RealWorld},
      Erasure.prepare_erasure e' s ctx cc rf w₀ = .ok (pe, s') w₁ → s'.gdecls = s.gdecls :=
    fun h => congrArg ErasureState.gdecls ((Hδ _ _).prep_run h).2
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
        hshape.closed
        (fun hb _ hlb hwf hnobv her =>
          -- Context-uniformity, DISCHARGED (δ-D7b): strengthen to `[]` through the one
          -- named obligation, then re-widen to *every* context with `erases_weak_any`.
          erases_uniform_closed henv hnfv hstr (VLCtx.FVLift.from_nil hnobv) hwf
            ((Hδ cctx ref).esrc_shape hb).1
            ((Hδ cctx ref).esrc_shape hb).2.choose_spec hlb her _)
        (visitExpr_noBlockEnv hprepg hvis noBlockEnv_empty))
  obtain ⟨t', heval, htrv, herv, hnbv, huniq⟩ :=
    shipping_erase_correct_firstorder henv (Us := [])
      (Esrc := Esrc.walked Γ sf.gdecls) (E := sf.gdecls) (known := known)
      hcon.walked
      hdelta
      (erasesEnvCtor_of_registeredCtors (hshape.registeredCtors (Hr.satCtors hvis)))
      hcc (recEnvConsistent_of_noRec hnorec) hnfv H HD C Hδ
      hvis hinv hsup htr (visitExpr_noBlock hvis) (hev hpr hvis) hfo
  exact ⟨sf.gdecls, t, t', hp, heval, htrv, herv, hnbv, huniq⟩

/-! ## The `hnorec` trade, and why its capstone half cannot be landed first

Slice δ-D8e checked whether the capstones could drop `hnorec` *now*, taking the
registration agreement (`hcov`: "`Γ` records as recursive only blocks the run really
stored") in its place and deriving `RecEnvConsistent` from the δ record the walk already
carries. They cannot, and the reason is worth recording, because the change would *look*
like a widening.

`DeltaMem` is keyed on the recorded entry and says nothing about its shape, so a `.fix`
entry is inside its statement already — that half composes. What does not is the supply:
the only exit that ever cons a `.constantDecl ⟨some (.fix …)⟩` is the recursive one, which
`DeltaHyps.nonrecursive` refutes on the fragment, and the *non-recursive* exit provably
cannot produce one — it stores a `visitExpr` output, and those are `NoFix`
(`nonrec_exit_stores_no_fix` below). So at a cold start no `.fix` entry exists, an
`hcov` premise phrased on membership is uninhabited for every `n` with
`Γ.recBodies n ≠ none`, and the "widened" capstone would speak about exactly the same
programs as the `hnorec` one — while hiding the restriction inside a premise instead of
naming it in the ledger. The trade waits for its producer, which is step 6's recursive
branch; see residue 1. -/

/-- **The non-recursive exit stores no block.** `visitMutual`'s non-recursive exit cons
exactly the `visitExpr` output it just built, and every such output is fix-free
(`ColdStartInduction.visitExpr_noFix_closed`, no hypotheses). So a `.fix` entry in
`gdecls` can only come from the recursive exit — the one the bridge's step 6 refutes on
the fragment. -/
theorem nonrec_exit_stores_no_fix {pe : Expr} {t : LBTerm} {s s' : ErasureState}
    {ctx : ErasureContext} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld}
    (hvis : Erasure.visitExpr pe s ctx cctx ref w = .ok (t, s') w')
    (defs : List (@FixDef LBTerm)) (j : Nat) : t ≠ .fix defs j := by
  intro h
  have hnf := (visitExpr_noFix_closed hvis).1
  rw [h] at hnf
  simp at hnf

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
    (hstr : ErasableStrengthen envFO [])
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
    (by simp [ΓFOι]) hstr Hr (by intro Δ n us body cve h; exact absurd h (by simp))
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
    (hstr : ErasableStrengthen envFO [])
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
    (by simp [ΓFOι]) hstr Hr (by intro Δ n us body cve h; exact absurd h (by simp))
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
    exact ⟨[], trivial, rfl, .ctor_head `c [] _ 0 ΓFOd_ctorsC⟩

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
      (by
        intro kn body hl
        obtain ⟨k, hmem, -⟩ := envLookup_mem hl
        simp only [sδ, Eδ, EFOd, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h | h
        · obtain rfl : body = tδ := (by simpa using h : k = toKername `g ∧ body = tδ).2
          simp [tδ, LBClosedArgs]
        · exact absurd h (by simp))
      (fun hb hm _ _ _ _ => by
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
    (hstr : ErasableStrengthen envδ [])
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
    (by simp [ΓFOd]) hstr Hr envδ_senvConsistent
    (by
      intro cn iid cidx hc
      by_cases h : cn = `c
      · subst h; rfl
      · simp [ΓFOd, if_neg h] at hc)
    H HD C Hδ S hev (envδ_foC_d harity) hrun

end DeltaGuard

end LeanToLambdaBox
