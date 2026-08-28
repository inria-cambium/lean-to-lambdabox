import LeanToLambdaBox
/-! Final axiom audit for the dev/verify verification stack (2026-07-07;
re-baselined 2026-08-10 for Lean v4.33.0-rc2 + the `barabbs/lean4lean` ι fork,
re-pinned 2026-08-11 to the reviewed ι interface `1a1ebe8` — head of the fork's
`iota` branch — and re-pinned again 2026-08-27 to `fee3ada` and then `7a5e96d`,
head of the fork's `trproj` branch, which is where `TrProj` stops being a `sorry`
and its motive gets pinned. The 7a5e96d step discharged no `sorry` and added no
axiom — lean4lean's own count holds at 143 across both revisions — and this file
reported the same 648 entries across it that it had reported immediately before it,
at slice Γ-W3b. [Corrected in the coherence pass, 2026-08-27: that sentence used to
read "the same 648 entries it did at `fee3ada`", which is false — at `fee3ada` this
file reported **596** (commit `5069f9d`); 648 is the Γ-W3b/`7a5e96d` figure, and the
596 → 648 growth is the Γ-W0…Γ-W3b slices, not a no-op re-pin.] It has grown thirteen
times since 648:
to 660 at slice proj-P3, to 673 at slice Γ-W3.5, to 691 at slice Γ-W3.6a, to 707 at
slice Γ-W3.6b, to 730 at slices proj-P0/P1/P4, to 750 at slice Γ-W4, to 772 at slice
proj-P2, to 800 at slices proj-P5/P6/P7, to 818 at slice proj-P8, to 850 at slice
proj-P9, to 856 at slice Γ-U, to 886 at slice Γ-W5 and to 910 at slice Γ-U1, with every earlier
entry's output byte-identical at each step — at proj-P8, proj-P9, Γ-U, Γ-W5 and Γ-U1 the whole
inherited prefix is (800, 818, 850, 856 and 886 entries respectively),
which is the strongest form of that claim the file can make and the one a slice adding
a premise to 33 signatures, and a slice growing the registry invariant, had to earn.
Γ-U earned it the easy way: it is an **analysis** slice — it changed no signature and
added only two guard theorems, because its finding is that the relaxation it was
commissioned to make would move the fragment's vacuity rather than remove it.
Γ-U1 earned it the same way, one step further: it is a pure lemma kit in one new file
(`ErasesLevels.lean`), with no consumer yet, so it edits no existing declaration at all —
its twenty-one entries are all `sorryAx`-free, and the 886-entry prefix was checked by
diffing a full run against a run of the same file with the new module stashed.
The projection round's model-layer entries are **all
`sorryAx`-free** bar one — proj-P2's
`Erases.strengthen_fvlift_binders`, which is the defeq-route strengthening and inherits the
same `TrProj.uniq` item `erases_strengthen_closed` has carried since `fee3ada`; that slice
kept the equational `Erases.strengthen_fvlift` beside it precisely so that no declaration
which was clean stopped being clean, and the 750-entry prefix confirms it. Γ-W4's twenty are
`sorryAx`-free too, bar the one that restates a first-order-value
fixture (`envRec_foC`, whose set is its `envFO`/`envδ` siblings' verbatim — the inherited
unique-typing item, reached through `IsDefEq.uniqU`).
The crown four did not move at any of them.

The projection round's **step** entries (P5/P6/P7) are the first of it to carry
`sorryAx`, and it is not new: `SEvalDataι_defeq` and `erases_correct_dataι` carried it
before the round and their sets are byte-identical after it, and `projConsistent_of_*`
inherits the same unique-typing item its ι twin `iotaConsistent_of_shape` does — with a
strictly smaller set, because a projection's reduct is a subterm and needs no application
generation. The round adds no axiom, no `sorry` and no `native_decide` of ours.

**The Γ-XL wave, closed.** Γ-W0 → Γ-W4 took the recursion wall down from both sides: the
bridge walks `visitMutual`'s recursive exit (Γ-W3.6b) and the capstones no longer exclude
recursive programs (Γ-W4). Over the wave's measured tail — Γ-W3.5 through Γ-W4, 673 → 746
entries — the crown four moved **once, and downward**, when the `trproj` re-pin took
`sorryAx` out of the refinement half. No slice of the wave added an axiom, a `sorry` or a
`native_decide`, and none changed a byte of the shipping eraser.)

Allowed: ⊆ [propext, sorryAx, Classical.choice, Quot.sound] + lean4lean's
modeling axioms (`Verify/Axioms.lean`, `PtrEq.lean`) where the executable
checker / `Expr` model is involved. The pure-LBTerm layers must be sorryAx-free.

## lean4lean-side baseline drift at the 2026-08-10 repoint

Nothing of ours changed: no axiom of ours was added, and every result below that
was sorryAx-free before is still sorryAx-free. The lean4lean modeling set moved:

* **Discharged upstream, so they no longer appear**: `Lean.Expr.hasFVar_eq`,
  `Lean.Expr.hasExprMVar_eq`, `Lean.Expr.hasLevelMVar_eq`,
  `Lean.Expr.hasLevelParam_eq` (now theorems) and `Lean.Expr.mkAppRangeAux.eq_def`
  (now proved).
* **Added upstream by the `Level` standardization**: `Lean.Level.normalize_eq`
  (reached by the deep kernel-checker cluster below), plus `Lean.Level.mkMaxAux_eq`,
  `Lean.Level.skipExplicit_eq`, `Lean.Level.isExplicitSubsumedAux_eq` (declared
  upstream, not reached from anything audited here).
* **`bv_decide` native-LRAT artifacts** from lean4lean's `Verify/Expr.lean`:
  `Lean.Expr.mkData_flags._native.bv_decide.ax_*` and
  `Lean.Expr.Data.looseBVarRange_le._native.bv_decide.ax_*`. lean4lean-side SAT
  certificates; they occur only in the executable-checker cluster (WS-O below).
* **`sorryAx` reach grew upstream** (the fork's twelve `IOTA-TODO(soundness)`
  items: `Aligned.addInduct`, `addInduct_WF`, the `IsDefEq`/`IsDefEqStrong` `pat`
  inversion cases, …). This widens the *inherited* trust boundary but does not
  reach any result here that was previously clean.

## The 2026-08-11 re-pin to the reviewed ι interface (`1a1ebe8`)

The fork's ι-witness commit was reviewed and landed as `1a1ebe8`; the statement of
`TrEnv.pats_iota'` — which `PatsIotaSpec` copies verbatim — is unchanged, and no
audited axiom set below moves. Two review-side facts worth recording:

* The reviewer **kept `TrEnv'.of_value` routed through `Aligned`** (rejecting the
  proposed `map_wf → constMap_wf` de-tainting), so `of_value` still inherits the
  `Aligned.addInduct` `sorry`. Nothing here uses it: the ι chain's δ step goes through
  `SEnvConsistent`. Same taint as at the previous pin, no drift.
* The fork's `sorry` count is unchanged (`Aligned.addInduct` and
  `VInductDecl.WF`'s inductive lemma remain), so the inherited boundary is the same.

New entry: `PatsIotaSpec.of_trEnv`, the discharge of `PatsIotaSpec` from a `TrEnv`.

## The 2026-08-27 re-pin to the TrProj delivery (`fee3ada`)

**This is the largest single movement the audit has ever recorded, and it is almost
entirely SHRINKAGE.** The commissioned round (A0–A3) gave `TrProj` a real definition —
an ι-pattern membership in `env.pats` plus a `HasType` conjunct — where the ι pin had a
`sorry`-valued `def`. Measured here, not quoted: `#print axioms Lean4Lean.TrProj` is now
`[propext]`.

That one fact is the whole story of the shrinkage. `sorryAx` used to enter this
development through the **type** of `TrExprS`, so *every* statement that so much as
mentioned `Erases`, `TrExprS`, `BridgeInv` or `DeltaHyps` carried it whether or not its
proof did anything projection-shaped. With the definition in place that channel is
closed, and what is left is only what the PROOFS actually use.

Measured old → new over this file's 584 entries:

* **139 entries (111 distinct declarations) LOST `sorryAx`**, gaining nothing.
* **3 entries (3 distinct declarations) GAINED two axioms** — see below.
* Entries carrying `sorryAx` at all: **230 → 91** (48 distinct declarations).
* Everything else is byte-identical, including the four crown theorems.

### The headline: the bridge is now sorryAx-free

`visitExpr_refines_erases` — the theorem that the shipping eraser refines `Erases` — and
its `_core` and `_block` forms now print

    [propext, Classical.choice, Quot.sound, Lean.Expr.instantiate1_eq,
     Lean.PersistentArray.toList'_push, Lean.PersistentHashMap.WF.find?_eq,
     Lean.PersistentHashMap.WF.toList'_insert]

with **no `sorryAx`**. So do `BridgeInv` and all its transports, `DeltaHyps`, `DeltaMem`,
`RunConclδ`, `ColdStartSubject`, `RecEnvConsistent`, every `Erases` transport lemma
(`abstract`, `uninstantiate{,N}`, `thin_vlet`, `strengthen_vlet`, `shift`, `subst`,
`weakFV`, `weak_any`, `fix_of_open{,_nil}`, `fix_of_closed`), the whole `registeredClosure`
/`erasesEnvDelta` δ family, `erases_rec_block_of_run`, `recEnvConsistent_of_block`, every
`g*` guard in that chain, and `PatsIotaSpec.of_trEnv` and `TrExprS.mkApps_inv` on the ι
side. The *refinement* half of the development no longer inherits anything from lean4lean
beyond the `Expr`/`PersistentHashMap` modelling axioms.

### What still carries `sorryAx`, and this is the provenance correction

The residue is now confined to the **forward-simulation** half — `erases_correct*`,
`eraseCore_correct`, the `SEval*` evaluation lemmas, the ι spine construction, and hence
the four capstones. Measured upstream at `fee3ada`, the live sources are:

1. **`Lean4Lean.TrExprS.uniq` → `Lean4Lean.TrProj.uniq`** — one of the two remaining
   `PROJ-TODO(soundness)` items. 69 downstream call sites of `.uniq`, 31 of them in
   `ErasesCorrectData.lean` alone, then `ErasesCorrect.lean` (11),
   `ErasesCorrectIota.lean` (7), `ErasesUniform.lean` (4), `FirstOrder.lean` (2),
   `ErasesStrengthen.lean` (2), `SubjectReductionFull.lean` (1). This is the densest
   single line of inherited debt in the development.
2. **`Lean4Lean.VEnv.IsDefEq.uniqU`** — the unique-typing development, `sorry`-carrying
   both through `IsDefEqU.weakN_iff` (which is exactly commission item C1, NOT discharged
   this round) and through the ι fork's `pat` cases. It reaches us through
   `TrProj.defeqDFC`, `TrExpr.app`/`TrExpr.proj`, and `TrExprS.instL` — note that
   `TrProj.instL` itself came back PROVED and clean (`[propext, Quot.sound]`); it is the
   `TrExpr` smart constructors around it that are dirty.
3. **`Lean4Lean.VEnv.HasType.app_inv`** (`Theory/Typing/Strong.lean`) — the ι spine
   construction, reaching `iotaConsistent_of_shape` and `iota_defeq_spine`.
4. **`Lean4Lean.Aligned.addInduct`** — the ι fork's environment-alignment `IOTA-TODO`.

**The two remaining `PROJ-TODO`s that do NOT reach us:** `TrProj.weak'_inv` (nothing here
calls `TrExprS.weakFV'_inv`/`weakFV_inv` — the `ErasesUniform` design deliberately routed
around it) and `TrEnv.proj_defeq` (a new interface, not yet consumed; see step 4 of the
consumability note in `ColdStart.lean`).

**Retired as sources, and every annotation in this file that named them is corrected in
place below:** `TrProj` the definition, `TrProj.weak'`, `TrProj.weakN`, `TrProj.mono`,
`TrProj.instL`, `TrProj.wf` — all proved upstream — and with them
`TrExprS.weakFV'`, `.weakBV`, `.mono`, `.instN`, `.weakFV`, `.inst`, `.weak_nil`,
`.mkApps_inv`, and `TrEnv.pats_iota'`, all now sorryAx-free.

### The growth, and it did NOT come from the commissioned work

`trproj` is a **merge of upstream `master`**, so this pin also absorbs master's
level-normalization rewrite, the K-target flag fix and `lazyDeltaProjReduction`. Two
axioms enter the audited surface with it:

* `Std.TreeMap.all_eq_all_toList` — a genuinely NEW `axiom` in lean4lean's
  `Verify/Axioms.lean` (added there together with `any_eq_any_toList`, which nothing here
  reaches), standing in for a `Std` lemma Lean does not yet prove
  (leanprover/lean4#12798).
* `Lean.Level.isExplicitSubsumedAux_eq` — declared upstream already at the `1a1ebe8` pin,
  and recorded above as "not reached from anything audited here". It is reached now, via
  master's `Verify/LevelStd.lean`.

Both arrive on the same path, the **executable kernel-checker cluster** — the same place
`Lean.Level.normalize_eq` already lived — and they touch exactly three entries:
`Lean4Lean.TypeChecker.kernel_isErasable_sound`, `ResidualHyps.toBridgeHyps`, and
`shipping_visitExpr_correct'`. They do NOT enter through the ι `_of_shape` cluster;
`iotaConsistent_of_shape` is byte-identical across the re-pin.

No axiom of ours was added. No `sorry` of ours exists.
-/

open LeanToLambdaBox

-- Task A: the de-partialized shipping family (must be sorryAx-free).
#print axioms Erasure.visitExpr.eq_def
#print axioms Erasure.visitLambda.eq_def
#print axioms Erasure.visitLet.eq_def
#print axioms Erasure.visitApp.eq_def
#print axioms Erasure.visitConstApp.eq_def
#print axioms Erasure.visitAppArgs.eq_def
#print axioms Erasure.visitMutual.eq_def
#print axioms Erasure.expr_withApp_eq

-- B1/B2: toBvar metatheory (must be lean4lean-free).
#print axioms toBvar_eq_of_not_hasFVar
#print axioms abstract_eq_of_not_hasFVar
#print axioms toBvar_shift
#print axioms toBvar_toBvar

-- B3/B3b: Erases transport (lean4lean boundary allowed).
#print axioms Erases.abstract
#print axioms Erases.uninstantiateN
#print axioms Erases.uninstantiate
#print axioms Erases.thin_vlet
#print axioms Erases.strengthen_vlet

-- Bridge part 1 (fragment + binder cores).
#print axioms Supported.instantiate1
#print axioms bridge_lam_case
#print axioms bridge_let_case
#print axioms TrLCtx.mkLocalDecl
#print axioms TrLCtx.mkLetDecl
#print axioms LocalContext.find?_mkLocalDecl_self
#print axioms LocalContext.fvarIdToDecl_find!_of_find?

-- B4 infra (must be lean4lean-free).
#print axioms Erasure.run_bind_ok
#print axioms Erasure.eraseM_admissible_ok
#print axioms Erasure.run_array_foldlM_ok
#print axioms Erasure.visitExpr_run_shape

-- Pre-existing flagship results (unchanged expectations).
#print axioms erases_correct
#print axioms eraseCore_correct
#print axioms isErasable.WF
#print axioms eval_deterministic
#print axioms LBOptimize_correct

-- B4 + Task C: the bridge and the top-level theorem.
#print axioms visitExpr_refines_erases
#print axioms shipping_visitExpr_correct

-- WS-F(theory): data-fragment widening (A3–A7). Expected: lean4lean boundary
-- (`[propext, sorryAx, Classical.choice, Quot.sound]`); A5 (`construct_app_spine`)
-- is sorryAx-free; `SEvalData`/`SEvalDataC` axiom-free.
#print axioms SEvalData
#print axioms SEvalDataC
#print axioms Erases.ctor_head
#print axioms SEvalData_const_spine_lam_elim
#print axioms construct_app_spine
#print axioms Erases.ctor_spine_inv
#print axioms erases_correct_data
-- WS-F2 (theory): ζ transport + ζ-including data simulation, and the ι subject
-- reduction. Expected: 4 standard + lean4lean `sorryAx`. [2026-08-27: the source is
-- the UNIQUE-TYPING cluster, not the projection one — `TrExprS.uniq`/`TrProj.uniq` and
-- `IsDefEq.uniqU`. These lemmas are genuine `.uniq` consumers, so unlike the transport
-- lemmas above they did NOT go clean at the `fee3ada` re-pin.]
-- `IotaConsistent` is a HYPOTHESIS of `SEvalDataι_defeq` (never an axiom), so it adds
-- nothing to the axiom set. (Still no `erases_correct_dataι`: `Erases.cases` now carries
-- the arity pins that unblock it — see the C3 status note in `SubjectReductionIota.lean` —
-- but the ι forward simulation itself is not built yet.)
#print axioms Erases.defeqDFC
#print axioms erases_correct_data_zeta
#print axioms SEvalDataι_defeq
#print axioms erases_correct_data_zeta_fires
#print axioms Erases_defeqDFC_fires
-- D0–D2: uniqueness of the applied erasure on first-order values.
#print axioms firstOrder_value_erases_unique
#print axioms firstOrderValue_erases_eq_eraseCore
#print axioms erases_correct_data_fires

-- WS-O: oracle-discharge stack (run-adequacy at ambient MLCtx + the discharge).
#print axioms Lean4Lean.TypeChecker.VContext.ofMLCtx
#print axioms Lean4Lean.TypeChecker.VState.WF.initial
#print axioms Lean4Lean.TypeChecker.M.WF.run'
#print axioms Lean4Lean.TypeChecker.kernel_isErasable_sound
#print axioms ResidualHyps.toBridgeHyps
#print axioms shipping_visitExpr_correct'

-- P3 (env-level erasure foundation): the `n`-way `closeFix` abstraction modelling the
-- `mkDef` closing loop. Pure LBTerm (imports only `Abstract`) — must be sorryAx-free.
#print axioms LeanToLambdaBox.closeFixFold_eq_foldl
#print axioms LeanToLambdaBox.closeFixFold_eq_self_of_not_hasFVar
#print axioms LeanToLambdaBox.closeFixFold_bvar
#print axioms LeanToLambdaBox.closeFixFold_fvar_of_not_mem
#print axioms LeanToLambdaBox.closeFixFold_fvar_head
#print axioms LeanToLambdaBox.closeFixFold_app
#print axioms LeanToLambdaBox.closeFix_2block_first
#print axioms LeanToLambdaBox.closeFix_2block_last

-- ============================================================================
-- P3-v2a: the `Erases.fix` rule bundle + its transport metatheory + the ripple.
-- The D3 capstone + the two data forward-sims must be UNCHANGED (4 standard +
-- lean4lean modeling set). The new transport/ripple theorems inherit `sorryAx`
-- from lean4lean's `TrExprS` lemmas (documented), no new axioms of ours.
-- ============================================================================
#print axioms shipping_erase_correct_firstorder
#print axioms shipping_visitExpr_correct_data
#print axioms erases_correct_data
#print axioms erases_correct_data_zeta
#print axioms erases_correct
#print axioms erases_correct_beta
-- new transport fix cases + ripple + rule guard:
#print axioms erases_shift
#print axioms erases_subst
#print axioms Erases.abstract
#print axioms Erases.thin_vlet
#print axioms Erases.lam_inv
#print axioms Erases.defeqDFC
-- Recursion wall, W1: the re-founded `Erases.fix` (source ↔ block link, registration,
-- `principalArgIdx = 0`, bodies against each def's unfolding), the `const_fix` leaf it
-- needs, their inversions and their constructed non-vacuity guards at a *genuinely
-- recursive* one-def block (`def f (a : Prop) := f a`). No new axiom of ours; the
-- `Erases`-mentioning results inherit `sorryAx` via the lean4lean `Expr` typing model.
#print axioms Erases.fix_inv
#print axioms Erases.const_inv
#print axioms LeanToLambdaBox.erases_const_fixRec
#print axioms LeanToLambdaBox.fixRecDefs_unfold
#print axioms LeanToLambdaBox.erases_fixRec
#print axioms noFix_subst1
#print axioms noFix_mkApps
-- Recursion wall, W2: the simulations unfold fix. `NoFixEnv E` and the `NoFix t`/
-- `NoFix t'` slots are GONE from `erases_correct`, `erases_correct_data`,
-- `erases_correct_data_zeta`, `erases_correct_dataι` and every capstone above; the
-- replacement is the registration-level `RecEnvConsistent`. (`erases_correct_beta` keeps
-- `NoFix t`: it has no environment at all, so its β-only fragment cannot meet a fix.
-- `NoFix` the predicate and its kit survive — see `noFix_subst1`/`noFix_mkApps` above —
-- they are simply no longer hypotheses of the general theorems.)
--
-- The chain kit is pure LBTerm/`WcbvEval` and must be sorryAx-free; `Erases.fix_unfold`
-- and `erases_lam_head_step` mention `Erases` and so inherit the standing lean4lean
-- boundary, exactly as their neighbours do. No new axiom of ours.
#print axioms LeanToLambdaBox.LBTerm.fix_or_not
#print axioms LeanToLambdaBox.FixUnfoldChain
#print axioms LeanToLambdaBox.FixUnfoldChain.eval
#print axioms LeanToLambdaBox.FixUnfoldChain.lbClosed
#print axioms LeanToLambdaBox.FixUnfoldChain.noBlock
#print axioms LeanToLambdaBox.fixUnfoldChain_selfLoop_step
#print axioms LeanToLambdaBox.Erases.fix_unfold
#print axioms LeanToLambdaBox.erases_lam_head_step
#print axioms LeanToLambdaBox.RecEnvConsistent
#print axioms LeanToLambdaBox.recEnvConsistent_of_noRec
#print axioms LeanToLambdaBox.recEnvConsistent_of_registeredClosureRec
-- W2's non-vacuity: the data simulation fires on a genuinely RECURSIVE program —
-- `def f (a : Prop) := f a` applied to a proof — where the target head is a `.fix` and the
-- step really is `fix_guarded` + `app_box`. This is the guard that makes the whole wall
-- witnessed rather than merely un-blocked.
#print axioms LeanToLambdaBox.erases_correct_data_recursive_fires
-- Recursion wall, W3.1: the `Erases.fixvar` leaf (`visitConst`'s `return .fvar id`) with
-- its rule-side freshness premise `x ∉ Δ.fvars`, and the `hnfv : Γ.fixvars = fun _ => none`
-- premise it forces onto the four forward simulations and every capstone above.
--
-- `ThinVLet.fvars_eq` is the one genuinely new pure lemma (the lean4lean-side
-- `Abstract`/`BVLift`/`InstN`/`InstLet` `fvars_eq`s already existed) and is axiom-free;
-- everything else mentions `Erases` and inherits the standing lean4lean boundary. No new
-- axiom of ours, and no axiom-set movement anywhere: every declaration listed here
-- reports exactly what it reported before the leaf landed.
#print axioms LeanToLambdaBox.ThinVLet.fvars_eq
#print axioms LeanToLambdaBox.Erases.const_inv_full
#print axioms LeanToLambdaBox.Erases.const_fvar_elim
#print axioms LeanToLambdaBox.erases_fixvar_fixOpen
#print axioms LeanToLambdaBox.erases_correct_data_zeta
-- …and the bridge side of W3.1: `BridgeInv.fixvars` is now an *agreement* between the
-- reader's block-local map and `Γ.fixvars` (plus `fixfresh`, the run's minting order),
-- `Supported.const` admits an in-block sibling, and motive 4 of the big induction
-- concludes `Erases.fixvar` on `visitConst`'s fixvar branch instead of killing it. The
-- big induction's axiom set is unchanged (it is re-listed at the cold-start block below).
#print axioms LeanToLambdaBox.Supported.const_inv'
#print axioms LeanToLambdaBox.BridgeInv.mkLocalDecl
#print axioms LeanToLambdaBox.BridgeInv.mkLetDecl
-- …and the Erases-level `visitMutual` correspondence, W3.1's last piece: the pure
-- `substFix` push-through kit (must be sorryAx-free — pure LBTerm), then
-- `Erases.instFixvars` (block-local erasure ⟹ erasure at the outer `Γ` with the fixvars
-- replaced by the block) and `erases_fix_of_open` (`erases_fix_of_closed` already composed
-- with it). `instFixvars` carries ONE `Prop` residue, `hnest` (a *nested* block inside a
-- body): `Erases.fix` records no fvar-freeness for its sibling **sources**, so its
-- `hbodies` cannot be transported. It is unreachable in the intended use — the eraser
-- emits `.const kn` at a call site, never a nested `.fix` — and it is a `Prop` hypothesis,
-- NEVER an axiom. `gInstFixvarsR` discharges it (by `id`) on the real fixture.
#print axioms LeanToLambdaBox.substFVar_eq_of_not_hasFVar
#print axioms LeanToLambdaBox.not_hasFVar_of_toBvar_eq_self
#print axioms LeanToLambdaBox.substFVarList_eq_self_of_not_hasFVar
#print axioms LeanToLambdaBox.substFix_fvar_getElem
#print axioms LeanToLambdaBox.substFix_mkLambdas
#print axioms LeanToLambdaBox.Erases.instFixvars
#print axioms LeanToLambdaBox.erases_fix_of_open
#print axioms LeanToLambdaBox.gErasesOpenR
#print axioms LeanToLambdaBox.gInstFixvarsR
-- P3-v1 (non-recursive + inductive cold-start env-consistency discharge). New trust is
-- Prop hypotheses (`PrepareHyps`, `Registered*`), NEVER axioms. Expected axiom set:
-- 4 standard [propext, Classical.choice, Quot.sound] (+ sorryAx via the lean4lean Expr
-- typing model where `Erases`/`TrExprS`/`BridgeInv` are involved). No axiom of ours.
#print axioms LeanToLambdaBox.PrepareHyps
#print axioms LeanToLambdaBox.prepareHyps_conclusion_at_identity
#print axioms LeanToLambdaBox.prepareHyps_inhabited_point
#print axioms LeanToLambdaBox.prepareHyps_csimp_off_satisfiable
#print axioms LeanToLambdaBox.ErasesEnvCases
#print axioms LeanToLambdaBox.erasesEnvCtor_of_registeredCtors
#print axioms LeanToLambdaBox.erasesEnvCases_of_registeredCases
#print axioms LeanToLambdaBox.gΓctor_registeredCtors
#print axioms LeanToLambdaBox.gΓctor_erasesEnvCtor
#print axioms LeanToLambdaBox.gΓcases_erasesEnvCases
#print axioms LeanToLambdaBox.erases_nonrec_const_body
#print axioms LeanToLambdaBox.erasesEnvDelta_of_registeredClosure
#print axioms LeanToLambdaBox.erasesEnvDeltaData_of_registeredClosureData
#print axioms LeanToLambdaBox.gRegisteredClosure
#print axioms LeanToLambdaBox.gErasesEnvDelta
#print axioms LeanToLambdaBox.gBridgeInv_nil

-- ============================================================================
-- P3-v2b: recursive (value-`fix`) cold-start env-consistency discharge.
-- New trust is Prop hypotheses (`RegisteredClosureRec`), NEVER axioms. The pure
-- `LBClosed` metatheory must be sorryAx-free; the `Erases.fix` reconciliation
-- inherits `sorryAx` only via the lean4lean Expr typing model (`Closed`/`FVarsIn`).
-- ============================================================================
#print axioms LeanToLambdaBox.LBClosed.shift_eq
#print axioms LeanToLambdaBox.LBClosed.subst_eq
#print axioms LeanToLambdaBox.erases_fix_of_closed
#print axioms LeanToLambdaBox.erasesEnvDelta_of_registeredClosureRec
#print axioms LeanToLambdaBox.gErases_fix
#print axioms LeanToLambdaBox.gRegisteredClosureRec
#print axioms LeanToLambdaBox.gErasesEnvDeltaRec

-- ============================================================================
-- ι-T4a/b: the `casesOn` bridge (`Supported.casesApp`, motives 15–18), now at
-- general λ-telescope alternatives. New trust is the `CasesBridgeHyps` **Prop**
-- bundle, NEVER an axiom. The `EraseM` loop rule, the pure `visitCases` loop
-- arithmetic and the `mkAlt`/`closeAlt` layer must be lean4lean-free (4 standard
-- at most); the fragment inversions, the telescope opener and the widened bridge
-- inherit `sorryAx` exactly as before, with no axiom of ours added. The `mkAlt`
-- name lookup and the lctx-persistence lemma go through lean4lean's
-- `PersistentHashMap`/`PersistentArray` modeling axioms, as `Bridge.lean`'s other
-- `find?` lemmas already do.
-- ============================================================================
#print axioms Erasure.run_list_forIn_ok'
#print axioms Erasure.run_array_forIn_ok'
#print axioms LeanToLambdaBox.IsLamTelescope.instantiate1'
#print axioms LeanToLambdaBox.exists_app_of_foldl_app_ne_nil
#print axioms LeanToLambdaBox.rco_toArray_getElem
#print axioms LeanToLambdaBox.slice_toArray_toList_drop
#print axioms LeanToLambdaBox.list_split_cases
#print axioms LeanToLambdaBox.subarray_next?_facts
#print axioms LeanToLambdaBox.visitCases_match_default
#print axioms LeanToLambdaBox.CasesBridgeHyps
#print axioms LeanToLambdaBox.CasesInfoAgrees
#print axioms LeanToLambdaBox.ForallMatchesLam
#print axioms LeanToLambdaBox.Supported.casesApp_inv
#print axioms LeanToLambdaBox.casesApp_spine_facts
-- ι-T4b: the λ-telescope layer.
#print axioms LeanToLambdaBox.ForallMatchesLam.instantiate1'
#print axioms LeanToLambdaBox.closeAlt_foldl
#print axioms LeanToLambdaBox.mkLambdas_closeAlt_cons
#print axioms LeanToLambdaBox.filter_replicate_keep
#print axioms LeanToLambdaBox.run_mkAlt
#print axioms LeanToLambdaBox.LocalContext.find?_mkLocalDecl_of_ne
#print axioms LeanToLambdaBox.LocalContext.fvarIdToDecl_find!_congr
#print axioms LeanToLambdaBox.bridge_alt_telescope

-- P3-v2b Part 4 + composition: recursion subsumed by v1's RegisteredClosure, and the
-- D3 capstone with env-δ-consistency sourced from registration. No axiom of ours.
#print axioms LeanToLambdaBox.registeredClosure_of_registeredClosureRec
#print axioms LeanToLambdaBox.erasesEnvDelta_of_registeredClosureRec'
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_registered

-- ============================================================================
-- ι Task 2: the pattern-side ι interface (`IotaPattern.lean`) + its guard
-- (`IotaDischarge.lean`).
--
-- The pure pattern plumbing (`Matches` introduction for spines, the
-- `SimplePattern.iotaRHS` reduct calculation) must be **sorryAx-free**: it touches
-- only `Pattern`/`VExpr`, never `TrExprS`.
--
-- REVISED 2026-08-27 at the `fee3ada` re-pin; the old reading of this block blamed
-- `TrProj`, and for two of the three entries below that is now simply false.
--
--   `TrExprS.mkApps_inv` is sorryAx-FREE. It is a pure `.app`-indexed `cases` inversion,
--     so its `sorryAx` was never anything but the definitional taint `TrProj` put in the
--     TYPE of `TrExprS`. A1 removed that taint and the entry went clean.
--   `PatsIotaSpec.of_trEnv` is sorryAx-FREE, because `TrEnv.pats_iota'` itself measures
--     clean at `fee3ada`. `PatsIotaSpec` remains a HYPOTHESIS structure, never an axiom,
--     and it remains DISCHARGED. What survives in its set is only lean4lean's three
--     `PersistentHashMap` `ConstMap` modelling axioms (`findAux_isSome`, `WF.find?_eq`,
--     `WF.toList'_insert`), which come in through the `constMap_wf`/`find?_insert` steps
--     of `pats_iota'`'s induction over `TrEnv'`. Still a strict SUBSET of
--     `shipping_visitExpr_correct'`'s, so nothing here is new, and it still does NOT pick
--     up `Aligned.addInduct` — `pats_iota'` is routed through `TrEnv'.constMap_wf`, not
--     `map_wf`.
--   `iota_defeq_spine` STAYS dirty, and for a reason that has nothing to do with
--     projections: it is a genuine consumer of the ι fork's `IsDefEq.pat` /
--     `Aligned.addInduct` sorries and of `VEnv.HasType.app_inv`. Its set is unmoved
--     across the re-pin, byte for byte.
--
-- The constructed guard `envι_iota_fires` must be **sorryAx-free**: it builds its
-- `VEnv` with `VEnv.addPat` directly and applies `VEnv.IsDefEq.pat`, neither of which
-- routes through `Aligned.addInduct`/`addInduct_WF`. (The δ-unfold step of
-- the remaining chain WOULD route through `Aligned.addInduct` via `TrEnv.of_value` —
-- documented in `IotaDischarge.lean`, not exercised here.)
-- ============================================================================
#print axioms Lean4Lean.Pattern.matches_varN_const
#print axioms Lean4Lean.Pattern.matches_iota
#print axioms Lean4Lean.SimplePattern.iotaRHS_apply
#print axioms Lean4Lean.TrExprS.mkApps_inv
#print axioms LeanToLambdaBox.PatsIotaSpec.of_trEnv
#print axioms LeanToLambdaBox.iota_defeq_spine
#print axioms LeanToLambdaBox.envι_iota_fires
-- The β-normalisation engine for steps (2)/(4)/(5). A β step builds its reduct's
-- `TrExprS` by `TrExprS.inst`, so it needs no application node — hence none of the
-- `HasType` premises that block the ι reduct. [2026-08-27: these two STAY dirty, and the
-- old "`TrProj` only" reading is wrong — `TrExprS.inst`/`.instN` are both sorryAx-free at
-- `fee3ada`. The `sorryAx` is the unique-typing cluster arriving through the `TrExpr`
-- layer these lemmas use to state their conclusions (`IsDefEq.uniqU`, hence C1, which the
-- trproj round did NOT discharge).]
#print axioms LeanToLambdaBox.trExprS_beta_step
#print axioms LeanToLambdaBox.trExprS_betaN

-- ι Task 2, part 2: `TrExprS` spine *construction* via application generation
-- (`Lean4Lean.VEnv.HasType.app_inv`, `Theory/Typing/Strong.lean` — a proved theorem at
-- this pin, whose sorry-frontier is a subset of the one `VEnv.IsDefEq.uniqU` already
-- carries), the `[] → Δ` transport of the fork-supplied rule template, and the payoff
-- `iotaConsistent_of_shape`.
--
-- `iotaConsistent_of_shape` picks up lean4lean's `Lean.Expr`-implementation modelling
-- axioms (`mkData_eq`, `mkAppData_eq`, `replace_eq`, `Level.hasMVar_eq`,
-- `Level.hasParam_eq`, `Level.instLawfulBEqLevel`, and two `bv_decide` native checks in
-- lean4lean's own `Expr.Data` bit-packing proofs) via `TrExprS.instL` — the price of
-- level-instantiating a polymorphic recursor rule. They are NOT new: its axiom set is a
-- strict SUBSET of the already-committed `shipping_visitExpr_correct'`'s. No axiom of
-- ours; `PatsIotaSpec`/`SEnvConsistent`/`IotaShape` are hypotheses, never axioms.
--
-- The two `IotaShape` `Expr`-equation guards must be `rfl`-provable and essentially
-- axiom-free (`[propext]`): they are closed `Expr` computations.
--
-- [2026-08-27, `fee3ada`: this block's provenance was already RIGHT — it named
-- `HasType.app_inv` and `IsDefEq.uniqU`, not `TrProj` — and it is the one ι block that
-- did not move. `iotaConsistent_of_shape` prints byte-identically across the re-pin, and
-- in particular it did NOT pick up master's `Std.TreeMap.all_eq_all_toList` /
-- `Lean.Level.isExplicitSubsumedAux_eq`; those enter only the executable-checker cluster.
-- One entry below DID go clean: `TrExprS.weak_nil`, which was carrying nothing but the
-- old definitional `TrProj` taint.]
#print axioms Lean4Lean.VExpr.WF.mkApps_head
#print axioms Lean4Lean.TrExprS.mkApps
#print axioms Lean4Lean.VEnv.IsDefEqU.mkApps_congr_head
#print axioms Lean4Lean.TrExprS.weak_nil
#print axioms Lean4Lean.TrExprS.instL_weak
#print axioms LeanToLambdaBox.iotaConsistent_of_shape
#print axioms LeanToLambdaBox.betaN_casesOn_guard
#print axioms LeanToLambdaBox.betaN_ruleTemplate_guard

-- ============================================================================
-- ι Task 3: the ι forward simulation (`ErasesCorrectIota.lean`), the `casesOn`-spine
-- erasure inversion (`ErasesCorrectData.lean`), the relocated closedness/de-Bruijn kit
-- (`Closed.lean`), and the Γ-population coherence discharge (`EnvErasureNonrec.lean`).
--
-- The `LBTerm` layers must be **sorryAx-free**: `Closed.lean` touches only `LBTerm`,
-- never `TrExprS`, so `LBClosed`'s metatheory and the general de Bruijn commutation kit
-- (`subst_subst` and friends) carry nothing beyond `propext`/`Quot.sound`.
--
-- [REVISED 2026-08-27, `fee3ada`: "everything that mentions `Erases`/`TrExprS` inherits
-- `sorryAx` from lean4lean's `TrProj` placeholder" was true at the ι pin and is FALSE
-- now. `TrProj` has a real definition and measures `[propext]`, so merely MENTIONING
-- `Erases`/`TrExprS` costs nothing. What is left in this section is dirty because its
-- PROOFS consume unique typing: the `casesOn`-spine inversions in `ErasesCorrectData.lean`
-- alone hold 31 of the 69 downstream `.uniq` call sites, and `.uniq` bottoms out in
-- `TrProj.uniq` (`PROJ-TODO`) and `IsDefEq.uniqU` (C1 + the ι `pat` cases). Section-local
-- effect of the re-pin: the `Erases` INVERSION and TRANSPORT lemmas went clean, the
-- SIMULATION lemmas did not.]
--
-- `IotaConsistent`, `PatsIotaSpec`, `IotaShape`, `IotaRelevant`, `ClosedEnv`,
-- `ErasesEnvCasesι`, `CtorFieldsCoherent`, `IotaArityCoherent` are all HYPOTHESES (Props
-- with constructed guards where constructible), never axioms, so they add nothing to any
-- axiom set below. `FlatCaseFields` is no longer a premise of anything (ι-S4b lifted the
-- flat-fields restriction); it survives only as the measure of that lift, guarded from
-- both sides by `gΓflat_flat` and `gΓfield_not_flat`.
-- ============================================================================

-- The de Bruijn / closedness kit: pure LBTerm, must be sorryAx-free.
#print axioms LeanToLambdaBox.LBClosed.mono
#print axioms LeanToLambdaBox.LBClosed.shift
#print axioms LeanToLambdaBox.LBClosed.subst
#print axioms LeanToLambdaBox.LBClosed.subst1
#print axioms LeanToLambdaBox.LBClosed.substList
#print axioms LeanToLambdaBox.LBClosed.mkApps
#print axioms LeanToLambdaBox.LBClosed.mkApps_inv
#print axioms LeanToLambdaBox.LBClosed.mkLambdas
#print axioms LBTerm.shift_shift
#print axioms LBTerm.subst_shift_cancel
#print axioms LBTerm.subst_shift_comm
#print axioms LBTerm.subst_subst
#print axioms LBTerm.substList_append
#print axioms LBTerm.substList_concat
#print axioms LBTerm.substList_reverse_subst

-- ι-S4b: the reversal bridge (`IotaBridge.lean`). Pure LBTerm + `WcbvEval` — no
-- `Erases`, no `TrExprS`, no lean4lean — so the whole module must be sorryAx-free,
-- including the two-field non-vacuity guard.
#print axioms LeanToLambdaBox.wcbvEval_mkApps_head_congr
#print axioms LeanToLambdaBox.value_mkApps_construct_args
#print axioms LeanToLambdaBox.wcbvEval_mkApps_mkLambdas_substList
#print axioms LeanToLambdaBox.wcbvEval_mkApps_mkLambdas_substList_fires
#print axioms LeanToLambdaBox.noBlock_mkLambdas
#print axioms LeanToLambdaBox.noFix_mkLambdas

-- `NoBlock`/`NoFix` traverse `.case`, and (recursion wall, W0.2) `NoBlock` also
-- traverses `.fix` via `NoBlockDefs` — `NoFix` needs no counterpart, being `False` on
-- `.fix` by construction. Their shift/subst preservation, and the new fix-unfolding
-- kit, must stay sorryAx-free (pure LBTerm).
#print axioms LeanToLambdaBox.noBlock_shift
#print axioms LeanToLambdaBox.noBlock_subst
#print axioms LeanToLambdaBox.noFix_shift
#print axioms LeanToLambdaBox.noFix_subst
#print axioms LeanToLambdaBox.NoBlockDefs_iff
#print axioms LeanToLambdaBox.NoBlock_fix
#print axioms LeanToLambdaBox.noBlock_substList
#print axioms LeanToLambdaBox.noBlock_fixSubst
#print axioms LeanToLambdaBox.noBlock_fixUnfold

-- Recursion wall, W0.3 (`FixUnfold.lean`): the `toBvar` ↔ `subst` commutation pair and
-- `closeFix_substList_fixSubst` — static fix-closing inverts dynamic fix-unfolding.
-- Pure LBTerm de Bruijn metatheory: no `Erases`, no `TrExprS`, no lean4lean, so the
-- whole module (including the non-vacuity witnesses) must be sorryAx-free.
#print axioms LeanToLambdaBox.LBClosed.substFVar
#print axioms LeanToLambdaBox.subst_toBvar_self
#print axioms LeanToLambdaBox.subst_toBvar_succ
#print axioms LeanToLambdaBox.closeFixFold_append
#print axioms LeanToLambdaBox.closeFix_cons
#print axioms LeanToLambdaBox.substList_toBvar
#print axioms LeanToLambdaBox.closeFix_substList_fixSubst_gen
#print axioms LeanToLambdaBox.closeFix_substList_fixSubst
#print axioms LeanToLambdaBox.closeFix_substList_fixSubst_fires
#print axioms LeanToLambdaBox.closeFix_substList_fixSubst_fires_value

-- Recursion wall, W0.1/W1 (`EnvErasureRec.lean`): the historical record that the
-- *pre-W1* `Erases.fix` was contentless, so `NoFix t` was load-bearing for *soundness*
-- in the forward simulations. The refutation now runs on the explicit hypothesis
-- `ContentlessFix` (what the pre-W1 rule handed out for free), and `not_contentlessFix`
-- records that slice W1 made that hypothesis refutable. `no_wcbvEval_app_gCxFix` is pure
-- `WcbvEval` and must be sorryAx-free; the refutation itself inherits `sorryAx` via
-- `TrExprS`, as every `Erases`-mentioning result does.
#print axioms LeanToLambdaBox.no_wcbvEval_app_gCxFix
#print axioms LeanToLambdaBox.gCxNoFixEnv
#print axioms LeanToLambdaBox.gCxSEval
#print axioms LeanToLambdaBox.gCxTrExprS
#print axioms LeanToLambdaBox.ContentlessFix
#print axioms LeanToLambdaBox.gCxErases
#print axioms LeanToLambdaBox.erases_correct_data_without_noFix_false_of_contentless_fix
#print axioms LeanToLambdaBox.not_contentlessFix

-- A6ι: the `casesOn`-spine erasure inversion and its exact-arity corollary.
-- Spine injectivity is pure `Expr` combinatorics (sorryAx-free); the inversions
-- themselves inherit `sorryAx` via `Erases`/`TrExprS`.
#print axioms LeanToLambdaBox.foldl_app_const_inj
#print axioms LeanToLambdaBox.Erases.app_inv_t
#print axioms LeanToLambdaBox.Erases.const_inv_full
#print axioms LeanToLambdaBox.Erases.cases_spine_inv
#print axioms LeanToLambdaBox.Erases.iota_redex_inv

-- C2, with `IotaConsistent` discharged, and the extracted ι reduct step.
#print axioms LeanToLambdaBox.SEvalDataι_iota_reduct
#print axioms LeanToLambdaBox.SEvalDataι_defeq_of_shape

-- The two-stage `IotaShape` guards (closed `Expr` computations, `rfl`).
#print axioms LeanToLambdaBox.betaN_ruleTemplate_eta_guard
#print axioms LeanToLambdaBox.betaN_ruleTemplate_rec_guard

-- C3: the ι forward simulation (any constructor arity, since ι-S4b), and the
-- source-side elimination it rests on. No axiom of ours.
#print axioms LeanToLambdaBox.SEvalDataι_partial_cases_lam_elim
#print axioms LeanToLambdaBox.erases_correct_dataι

-- Γ-population coherence: the non-Prop conjunct and the `CtorFieldsCoherent` discharge,
-- plus the constructed non-vacuity guards for every ι side condition except
-- `IotaRelevant` (see `ErasesCorrectIota.lean` for why that one has none at this pin).
#print axioms LeanToLambdaBox.ErasesEnvCases.nonProp
#print axioms LeanToLambdaBox.ctorFieldsCoherent_of_registered
#print axioms LeanToLambdaBox.gΓι_ctorFieldsCoherent
#print axioms LeanToLambdaBox.gΓι_iotaArityCoherent
#print axioms LeanToLambdaBox.gΓι_nonProp
#print axioms LeanToLambdaBox.gΓflat_flat
#print axioms LeanToLambdaBox.gΓflat_erasesEnvCasesι
#print axioms LeanToLambdaBox.gΓflat_ctorFieldsCoherent
#print axioms LeanToLambdaBox.gΓflat_iotaArityCoherent
#print axioms LeanToLambdaBox.gEcl_closedEnv

-- ι-S4b: the same certificate block at a FIELD-CARRYING `Γ` (`AC`, one parameter and
-- one field), i.e. outside the lifted flat restriction.
#print axioms LeanToLambdaBox.gΓfield_not_flat
#print axioms LeanToLambdaBox.gΓfield_erasesEnvCasesι
#print axioms LeanToLambdaBox.gΓfield_ctorFieldsCoherent
#print axioms LeanToLambdaBox.gΓfield_iotaArityCoherent
#print axioms LeanToLambdaBox.gΓfield_certificates

-- ============================================================================
-- ι Task 5: the ι capstone (`FirstOrderShippingIota.lean`) — D3 over `SEvalDataι`.
--
-- Three declarations, in the repo's interface/implementation shape:
--
--   * `shipping_erase_correct_firstorderι`          — `IotaConsistent` as the interface
--                                                     premise (as `SEvalDataι_defeq`);
--   * `shipping_erase_correct_firstorderι_of_shape` — with it DISCHARGED from
--                                                     `PatsIotaSpec + SEnvConsistent +
--                                                     IotaShape`;
--   * `shipping_erase_correct_firstorderι_registered` — every Γ/E env-consistency
--                                                     premise sourced from the
--                                                     registration records.
--
-- AXIOM EXPECTATION (measured, 2026-08-10):
--
--   `…firstorderι` and `…firstorderι_registered` print the axiom set of
--   `shipping_erase_correct_firstorder` **verbatim** — 4 standard + the 4 lean4lean
--   `Lean.Expr`/`PersistentHashMap` modelling axioms. The ι machinery contributes
--   nothing: `erases_correct_dataι` is [propext, sorryAx, Classical.choice, Quot.sound],
--   and every ι side condition (`IotaConsistent`, `IotaRelevant`, `IotaShape`,
--   `IotaArityCoherent`, `CtorFieldsCoherent`, `ClosedEnv`, `ErasesEnvCases(ι)`,
--   `PatsIotaSpec`) is a `Prop` HYPOTHESIS, never an axiom. (`FlatCaseFields` was one
--   too, and is gone from the capstones entirely since ι-S4b.)
--
--   `…firstorderι_of_shape` prints those EIGHT MORE, and only these eight:
--
--     Lean.Expr.mkAppData_eq, Lean.Expr.mkData_eq, Lean.Expr.replace_eq,
--     Lean.Level.hasMVar_eq, Lean.Level.hasParam_eq, Lean.Level.instLawfulBEqLevel,
--     Lean.Expr.mkData_flags._native.bv_decide.ax_1_12,
--     Lean.Expr.Data.looseBVarRange_le._native.bv_decide.ax_1_7
--
--   They enter through `iotaConsistent_of_shape` → `TrExprS.instL` (level-instantiating
--   a polymorphic recursor rule) and are lean4lean's own `Lean.Expr`/`Lean.Level`
--   implementation-model axioms plus its two `bv_decide` SAT certificates. They are NOT
--   new: this eight-element set is a strict SUBSET of the already-committed
--   `shipping_visitExpr_correct'`'s (printed above). NO AXIOM OF OURS, anywhere.
--
--   Note the earlier T2 note is about `iotaConsistent_of_shape` vs
--   `shipping_visitExpr_correct'` (the *primed* theorem, the executable-checker
--   cluster) — NOT vs `shipping_erase_correct_firstorder`, whose set is much smaller.
--   Hence the eight-axiom delta on the `_of_shape` form is expected, not a regression.
--
-- The Γ/E certificate block guards must be **sorryAx-free**: they are pure
-- `ErasureCtx`/`GlobalDeclarations` computations, with no `Erases`/`TrExprS` content.
-- `envFO_foC_ι` inherits `sorryAx` via `TrExprS`, as `envFO_foC_d` already does.
-- ============================================================================

-- The capstone, and the non-ι one immediately before it for a direct comparison.
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_registered
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_registered
-- The discharged form: the eight-axiom delta enumerated above.
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_of_shape

-- The certificate block, jointly constructed at one registered *flat* inductive
-- (`ΓFOι`/`iaFOι`/`EFOd`) — the guard the ι capstone can carry. The end-to-end guard in
-- which the ι rule itself contracts a real pattern match is blocked by the upstream
-- `VEnv.WF`-unconstructible-for-`pats` obstruction; see `FirstOrderShippingIota.lean`.
--
-- Recursion wall, W2: the block's `NoFixEnv EFOd` conjunct became
-- `RecEnvConsistent envFO [] ΓFOι (fun _ => none) EFOd` (the sims' new premise), so the
-- block's *statement* now mentions `Erases` and therefore inherits the standing lean4lean
-- boundary — `ΓFOι_certificates` picks up `sorryAx` where it previously had none. This is
-- statement-level inheritance, not a new proof obligation: the witness is
-- `recEnvConsistent_of_noRec rfl` (`ΓFOι` registers no recursion), and `Erases` itself has
-- carried `sorryAx` since it was defined (see `#print axioms Erases`). Every capstone that
-- consumes this block already had the same set.
#print axioms LeanToLambdaBox.ΓFOι_certificates
#print axioms LeanToLambdaBox.ΓFOι_registeredCtors
#print axioms LeanToLambdaBox.ΓFOι_registeredCases
#print axioms LeanToLambdaBox.ΓFOι_registeredCtorFields
#print axioms LeanToLambdaBox.ΓFOι_erasesEnvCtor
#print axioms LeanToLambdaBox.ΓFOι_erasesEnvCasesι
#print axioms LeanToLambdaBox.ΓFOι_ctorFieldsCoherent
#print axioms LeanToLambdaBox.ΓFOι_iotaArityCoherent
#print axioms LeanToLambdaBox.EFOd_closedEnv
#print axioms LeanToLambdaBox.EFOd_noFixEnv
#print axioms LeanToLambdaBox.envFO_foC_ι

-- ============================================================================
-- The Nat-literals wall, slices L1 + L2 (`Erases.lit`, and the literal source /
-- target semantics).
--
-- `Erases.lit` mirrors lean4lean's `TrExprS.lit`: a `.lit l` erases to whatever its
-- one-step constructor unfolding `Literal.toConstructor` erases to. Under
-- `nat := .peano` that unfolding *is* the shipping `visitLiteral`, so the applied-form
-- peano tower comes out of the existing `ctor_head`/`app` rules and no new target-side
-- machinery (`WcbvEval`, `FirstOrderValue`, `eraseCore`) is involved. Machine-`Nat`
-- (`.prim`) remains out of scope, so the machine-mode results are unchanged.
--
-- The literal fragment adds **no axiom of ours**: `TrExprS.lit_inv'` is a one-line
-- `cases` on `TrExprS.lit` (no `sorry`-carrying lemma, unlike the projection case), so
-- everything below carries exactly the boundary its neighbours already carried.
-- ============================================================================

-- L1: the literal inversions (both sides) and the two spine-shape helpers.
#print axioms LeanToLambdaBox.TrExprS.lit_inv'
#print axioms LeanToLambdaBox.foldl_app_const_ne_lit
#print axioms LeanToLambdaBox.foldl_app_cons_ne_lit
#print axioms LeanToLambdaBox.Erases.lit_inv

-- L1: the six enumerated `Erases` inductions, re-audited with the `lit` arm.
#print axioms LeanToLambdaBox.erases_shift
#print axioms LeanToLambdaBox.erases_subst
#print axioms LeanToLambdaBox.erases_subst_let
#print axioms LeanToLambdaBox.Erases.abstract
#print axioms LeanToLambdaBox.Erases.thin_vlet
#print axioms LeanToLambdaBox.Erases.defeqDFC

-- L1 guard: the tower is really derivable, at a constructed `env` (so `ContainsLits`
-- is proved, not assumed) and a peano `Γ`.
#print axioms LeanToLambdaBox.envNatLit_containsLits
#print axioms LeanToLambdaBox.ΓnatLit_zero
#print axioms LeanToLambdaBox.ΓnatLit_succ
#print axioms LeanToLambdaBox.erases_natLit

-- L2: subject reduction over the literal rule is `refl` (source and unfolding share the
-- `VExpr`), and the three forward simulations absorb it by their IH.
#print axioms LeanToLambdaBox.SEvalData.toβζδ
#print axioms LeanToLambdaBox.SEvalDataC.toSEvalData
#print axioms LeanToLambdaBox.SEvalData_const_spine_lam_elim
#print axioms LeanToLambdaBox.SEvalβζδ_defeq
#print axioms LeanToLambdaBox.SEvalDataι_defeq
#print axioms LeanToLambdaBox.erases_correct_data
#print axioms LeanToLambdaBox.erases_correct_data_zeta

-- L2 guard: the literal runs on both sides and the two are linked — the target tower is
-- a `WcbvEval` value via `construct_atom`/`construct_app` alone.
#print axioms LeanToLambdaBox.EnatLit_arity_zero
#print axioms LeanToLambdaBox.EnatLit_arity_succ
#print axioms LeanToLambdaBox.erasesEnvCtor_natLit
#print axioms LeanToLambdaBox.wcbvEval_natLitTower
#print axioms LeanToLambdaBox.noBlock_natLitTower
#print axioms LeanToLambdaBox.noFix_natLitTower
#print axioms LeanToLambdaBox.sevalData_natLit
#print axioms LeanToLambdaBox.erases_srcNatTower

-- ============================================================================
-- COLD-START SLICE S1 (2026-08-12): the registration-path run lemmas and the
-- registry invariant `RegInvShape`.
--
-- Everything here is pure `EraseM`-run / `GlobalDeclarations` reasoning: no
-- `Erases`, no `TrExprS`, no lean4lean. Expected axiom set for every entry below:
-- ⊆ [propext, Classical.choice, Quot.sound]. **No `sorryAx`** — in particular the
-- run lemmas do not inherit lean4lean's, since they never touch the model.
--
-- What changed in the trust ledger:
--
--   * `Erasure.run_getConstInfo_state` (and `run_getEnv_state`,
--     `run_mkFreshFVarId_state`, `run_logInfo_state`) are THEOREMS. The
--     `s = s₁` clauses that `DataBridgeHyps.ctorinfo_run`/`indinfo_run`/
--     `extern_run` and `CasesBridgeHyps.casesind_run` assume for those very
--     primitives are therefore redundant — they can be dropped from the bundles.
--
--   * `Erasure.run_register_inductive_cold_ok` shows the cold branch conses one
--     `.inductiveDecl` entry (plus one axiom entry per `@[extern]` constructor).
--     `DataBridgeHyps.reg_run` and `CasesBridgeHyps.casesreg_run` asserted
--     `s = s₁` for `register_inductive` over an ARBITRARY `s`, which this
--     refutes as a statement about the real function. REPAIRED in slice S2
--     (below): both clauses are gone, and the counter-argument against the
--     D3/D3ι `_registered` capstones' premise set is retired with them.
--
--   * `Erasure.run_addAxiom_ok` records the panic fall-through (`addAxiom`'s
--     guard has no `return`, and `panic!` succeeds at `EraseM`), so the post-state
--     is the modified one on BOTH branches.
-- ============================================================================

#print axioms Erasure.run_addAxiom_ok
#print axioms Erasure.run_register_inductive_hit_ok
#print axioms Erasure.run_register_inductive_cold_ok
#print axioms Erasure.run_get_constant_kername_ok
#print axioms Erasure.run_mkDef_ok
#print axioms Erasure.run_modify_forIn_ok
#print axioms Erasure.run_getConstInfo_state
#print axioms Erasure.run_getEnv_state
#print axioms Erasure.run_logInfo_state
#print axioms Erasure.run_mkFreshFVarId_state

-- The invariant, its cold-start base case, its collapse to the capstones' premise
-- set, and its preservation along the registration primitives (from the run).
#print axioms LeanToLambdaBox.envLookup_append_of_fresh
#print axioms LeanToLambdaBox.RegInvShape.empty
#print axioms LeanToLambdaBox.RegInvShape.registeredCtors
#print axioms LeanToLambdaBox.RegInvShape.registeredCases
#print axioms LeanToLambdaBox.RegInvShape.registeredCtorFieldsAll
#print axioms LeanToLambdaBox.RegInvShape.noFixEnv
#print axioms LeanToLambdaBox.RegInvShape.closedEnv
#print axioms LeanToLambdaBox.RegInvShape.addAxiom_run
#print axioms LeanToLambdaBox.RegInvShape.register_inductive_run
-- The obligation the shape induction still owes at `visitMutual`'s non-recursive
-- constant cons — an IFF, hence not dischargeable by state reasoning. This is why the
-- design's "optional" output-shape motives (R11) are in fact a prerequisite of S1.
#print axioms LeanToLambdaBox.regInvShape_nonrec_cons_iff
-- Non-vacuity: the invariant survives genuine registration steps.
#print axioms LeanToLambdaBox.gRegInvShape_addAxiom
#print axioms LeanToLambdaBox.gRegInvShape_addAxiom₂

-- ============================================================================
-- COLD-START SLICE S1b (2026-08-12): `visitMutual`'s exits, and the binder
-- metatheory the output-shape induction needs.
--
-- Same expectation: ⊆ [propext, Classical.choice, Quot.sound], no `sorryAx`.
--
--   * `Erasure.run_visitMutual_ok` is the DAG engine's Hoare rule over its four
--     exits (axiom / non-recursive constant / recursive block / inlining-only
--     bookkeeping). It takes the `visitExpr` fact as a HYPOTHESIS, so it is
--     usable inside `visitExpr.mutual_fixpoint_induct` — where the step goals
--     are about an abstract function, not the real `visitExpr` — as well as
--     standalone. The recursive exit is *handled*, not refuted: `hrec` receives
--     the `.fix` conses, which is what lets `RegInvShape`'s disjunctive `nofix`
--     absorb the recursion wall with no restructuring.
--
--   * Exactly one hypothesis of `run_visitMutual_ok` is assumed rather than
--     proved: `hprep`, that `prepare_erasure` leaves the predicate alone. Its
--     `csimp` branch runs `Lean.Core.transform` *at* `EraseM` through
--     `MonadControlT`, so state transparency does not follow from the `liftM`
--     lemmas. It belongs with `PrepareHyps`. Slice S4's `erase_run_ok` (R1)
--     needs the same fact.
--
--   * `LeanToLambdaBox.OutputShape` supplies the binder metatheory: `toBvar`
--     preserves `NoFix` and shifts `LBClosed` by one level, plus the fold forms
--     `mkAlt`/`mkDef` need.
-- ============================================================================

#print axioms Erasure.run_inline_tail_ok
#print axioms Erasure.run_inline_prefix_ok
#print axioms Erasure.run_nonrec_exit_ok
#print axioms Erasure.run_rec_exit_ok
#print axioms Erasure.run_visitMutual_ok
#print axioms LeanToLambdaBox.noFix_toBvar
#print axioms LeanToLambdaBox.lbClosed_toBvar
#print axioms LeanToLambdaBox.noFix_foldl_toBvar
#print axioms LeanToLambdaBox.lbClosed_foldl_toBvar
#print axioms LeanToLambdaBox.lbClosed_foldl_zipIdx
-- The `RegInvShape` closure lemmas `run_visitMutual_ok` consumes at two of its four
-- exits. The recursive exit's (`RegInvShape` under `Erasure.recConstState`) is the one
-- piece of the R7 interface still open.
#print axioms LeanToLambdaBox.RegInvShape.inlinings
#print axioms LeanToLambdaBox.RegInvShape.nonrecConst

-- ============================================================================
-- COLD-START SLICE S1c (2026-08-12): the recursive exit's closure lemma, and the
-- binder-helper run lemmas the output-shape induction steps through.
--
-- Same expectation: ⊆ [propext, Classical.choice, Quot.sound], no `sorryAx`.
--
--   * `RegInvShape.recConst` completes the `run_visitMutual_ok` interface: all
--     four exits now have their closure lemma. Its two inputs are honest
--     assumptions, not gaps in the argument: `KeysDistinct` of the final
--     `gdecls` (nothing in `visitMutual` rules out shadowing — it tests neither
--     `s.gdecls` nor `s.constants` before consing), and closedness of the stored
--     `.fix` bodies (the recursion wall's `closeFix` result).
--
--   * `RegInvShape.constCons` generalises `nonrecConst`: the stored body may be
--     plain (`NoFix`) or a literal `.fix`, which is exactly the disjunction
--     `NoFixEnvD` carries. The recursive and non-recursive exits are then the
--     same lemma at the two disjuncts.
--
--   * The binder-helper run lemmas each carry an `r = default` fall-through
--     disjunct: every destructuring helper `panic!`s on a shape mismatch, and a
--     panic SUCCEEDS at `EraseM`. That is the code's real behaviour.
-- ============================================================================

#print axioms LeanToLambdaBox.RegInvShape.constCons
#print axioms LeanToLambdaBox.recConstFold_gdecls
#print axioms LeanToLambdaBox.RegInvShape.recConstFold
#print axioms LeanToLambdaBox.RegInvShape.recConst
#print axioms Erasure.run_withLocalDecl_ok
#print axioms Erasure.run_withLocalDef_ok
#print axioms Erasure.run_lambdaMonocular_ok
#print axioms Erasure.run_letMonocular_ok
#print axioms Erasure.run_forallMonocular_ok
#print axioms Erasure.run_lambdaMonocularOrIntro_ok
#print axioms Erasure.run_lambdaOrIntroToArity_ok
#print axioms Erasure.run_fvar_to_name_ok
#print axioms Erasure.run_mkLambda_ok
#print axioms Erasure.run_mkLetIn_ok
#print axioms Erasure.run_mkAlt_ok

-- ============================================================================
-- COLD-START SLICE S1d (2026-08-12): the output-shape induction (R11).
--
-- Same expectation: ⊆ [propext, Classical.choice, Quot.sound], no `sorryAx`.
-- This layer is pure `LBTerm`/`EraseM` reasoning — it touches neither lean4lean
-- nor the `Erases` relation — so the bound is tight, not inherited.
--
--   * `visitExpr_shape` is the 18-motive fixpoint induction over the erasure
--     family, in Hoare form over a state predicate `Q` closed under the six
--     places the family writes to `ErasureState` (`RunClosed`). Stating it over
--     an abstract `Q` is what lets `visitMutual` — the only writer — be handled
--     INSIDE the induction, where the step goal mentions the fixpoint's abstract
--     `visitExpr` argument rather than the real function.
--
--   * `visitExpr_noFix_closed` is R11 with NO hypotheses: `RunClosed` holds
--     outright at `fun _ => True` (`runClosed_true`), which collapses the state
--     half and leaves "every successful `visitExpr` run returns a fix-free,
--     de-Bruijn-closed term". That is exactly the obligation
--     `regInvShape_nonrec_cons_iff` proved the registry invariant owes at
--     `visitMutual`'s non-recursive constant cons — so S1's last prerequisite is
--     discharged, and `runClosed_true` doubles as the class's non-vacuity guard.
--
--   * `RunClosed.regInvShape` instantiates the induction at `RegInvShape Γ`.
--     Four of the six closure fields are PROVED from S1's step lemmas; what is
--     left sits in one named record, `RegShapeHyps`, of exactly two kinds — key
--     freshness (the code tests neither `s.gdecls` nor injectivity of
--     `toKername`) and `Γ`-agreement for the block being registered (slice S4's
--     `RegBridgeHyps`) — plus `recClosed` (the recursion wall's `closeFix`
--     result) and `prep` (`PrepareHyps` class, as in R7).
--
--   * The two matcher lemmas are stated against elaborator-generated matchers
--     (`visitCases.match_7`, `visitConstructor.match_1`): name-pattern matchers
--     compile to `Name.rec` + `String` `dite`s that `split` cannot take apart at
--     a hypothesis whose subject is the match APPLIED to the monad's arguments.
--     If either shipping match is edited the index moves — build error, not
--     unsoundness.
--
--   * `run_nonrec_exit_ok` / `run_rec_exit_ok` were generalized over the erasure
--     function (`{vE : Expr → EraseM LBTerm}`) for this induction; strictly more
--     general, `run_visitMutual_ok` instantiates `vE := visitExpr`.
-- ============================================================================

#print axioms LeanToLambdaBox.noFix_default
#print axioms LeanToLambdaBox.lbClosed_default
#print axioms LeanToLambdaBox.visitCases_match_tri
#print axioms LeanToLambdaBox.visitConstructor_match_quad
#print axioms LeanToLambdaBox.visitExpr_shape
#print axioms LeanToLambdaBox.runClosed_true
#print axioms LeanToLambdaBox.visitExpr_noFix_closed
#print axioms LeanToLambdaBox.visitExpr_output_shape
#print axioms LeanToLambdaBox.RunClosed.regInvShape
#print axioms LeanToLambdaBox.visitExpr_regInvShape
#print axioms LeanToLambdaBox.visitMutual_regInvShape
#print axioms LeanToLambdaBox.get_constant_kername_regInvShape

-- ============================================================================
-- COLD-START SLICE S2 (2026-08-12): the bridge goes cold-startable.
--
-- Expectation: the bridge keeps its lean4lean boundary
-- (`[propext, sorryAx, Classical.choice, Quot.sound]` + the `Expr`/`PersistentX`
-- modeling axioms); the new `ErasureRun` layer is ⊆ [propext, Classical.choice,
-- Quot.sound], no `sorryAx` — it is pure `EraseM` state reasoning.
--
-- WHAT CHANGED IN THE TRUST LEDGER — six assumed clauses deleted, none added:
--
--   * PROVABLE, hence deleted: the `s = s₁` conjuncts of
--     `DataBridgeHyps.ctorinfo_run` / `indinfo_run` / `extern_run`,
--     `CasesBridgeHyps.casesind_run`, and `BridgeHyps.fresh_run` /
--     `ResidualHyps.fresh_run`. The bridge now derives each from
--     `Erasure.run_getConstInfo_state` / `run_getEnv_state` /
--     `run_mkFreshFVarId_state`.
--
--   * FALSE, hence deleted: the `s = s₁` conjuncts of `DataBridgeHyps.reg_run`
--     and `CasesBridgeHyps.casesreg_run` (S1's finding above). They are NOT
--     re-added under a pre-registration precondition — the call sites cannot
--     establish one — and the remaining content of both fields (`r.1 = iid`, the
--     trivial argmasks) is branch-independent. What replaces them is a THEOREM,
--     `Erasure.run_register_inductive_runConcl`, assembled from R5 (hit branch:
--     state preserved) and R4 (miss branch: state only grows).
--
--   * The one side condition ADDED is not a trust assumption but a constraint on
--     the parameter `Γ`: `BridgeInv.knames` (`Γ.constants = toKername`, the
--     design's `hknames`). It is discharged at every concrete `Γ` in the
--     development (`ΓFOd`/`ΓFOι` define `constants := toKername`) and is passed
--     explicitly through the guards below.
--
-- WHAT THE BRIDGE NOW CONCLUDES: `s' = s` widened to `Erasure.RunConcl s s'` —
-- `StateLe` (both registries grow, `gdecls` is only prepended to) plus
-- preservation of `CanonicalConstants`. `BridgeInv.consts` went from
-- completeness (`known n → s.constants.get? n = some (Γ.constants n)`) to
-- soundness (`s.constants.get? n = some k → k = Γ.constants n`, i.e.
-- `RegInvShape.kn`), which is what survives state growth; the completeness
-- direction survives only as `known_dom` (domain membership, monotone in
-- `StateLe`).
--
-- [SUPERSEDED by δ-D4a, below: motive 6 has content, motive 5's miss branch is
-- proved, and `known_dom` is deleted. The diagnosis in this paragraph is right
-- about what it costs and wrong about where it lives — the fix was not a new
-- `RegBridgeHyps` field but the scope-side bundle `DeltaHyps`.]
--
-- WHAT DID NOT LAND: motive 6 (`visitMutual`) stays `True` and motive 5's MISS
-- branch stays refuted by `known_dom` rather than proved. The design's §5.3
-- claim that the miss branch "discharges from slice 1's motive 6" does not go
-- through: S1's `visitMutual_regInvShape` is about the REAL `visitMutual`, while
-- the bridge's step 5 sees the fixpoint's abstract approximation, and giving
-- motive 6 real content inside this induction requires the abstract `visitExpr`
-- to deliver `NoFix`/`LBClosed` of its output (`RunClosed.nrc`) — i.e. merging
-- the whole S1d induction into this one. Independently, motive 5's miss branch
-- would need two facts unavailable here: that `visitMutual n` registers `n`
-- (its recursive exit registers the block names read out of the opaque
-- `Compiler.LCNF.getDeclInfo?`) and generator-monotonicity of `visitMutual`'s
-- primitives. Both are `RegBridgeHyps`-class obligations of the cold-start
-- entry slice (S4), where the design already places them.
-- ============================================================================

#print axioms Erasure.StateLe
#print axioms Erasure.StateLe.trans
#print axioms Erasure.RunConcl
#print axioms Erasure.RunConcl.trans
#print axioms Erasure.run_register_inductive_runConcl
#print axioms LeanToLambdaBox.BridgeInv
#print axioms LeanToLambdaBox.BridgeInv.mono_state
-- The bridge and its consumers, re-checked under the widened conclusion.
#print axioms LeanToLambdaBox.visitExpr_refines_erases_core
#print axioms LeanToLambdaBox.visitExpr_refines_erases
#print axioms LeanToLambdaBox.shipping_visitExpr_correct_data
#print axioms LeanToLambdaBox.erases_nonrec_const_body
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_registered

-- ============================================================================
-- The Nat-literals wall, slice L3 (2026-08-12): the fragment and the bridge.
--
-- The literal now has a `Supported` rule and a `visitExpr` dispatch, so the wall's
-- model core (L1) and its source/target semantics (L2) are reachable from the shipping
-- eraser. Three statement changes, all additive or vacuous-at-the-default:
--
--   * `Supported.natLit` — a `Nat` literal at a `Γ` that declares peano mode
--     (`Γ.natPeano`, `ErasureContext.lean`) and registers `Nat`'s two constructors at
--     their real kernel indices. `.strVal` stays out at EVERY `Γ` (the shipping
--     `visitLiteral` `panic!`s on it); machine-`Nat` stays out because at
--     `Γ.natPeano = false` the rule is unusable — both are guarded in `Bridge.lean`.
--
--   * `BridgeInv.natcfg : Γ.natPeano = true → ctx.config.nat = .peano` — the config pin.
--     `Supported` is syntactic in `(known, Γ)` and cannot see the reader's config, so
--     the flag lives in `Γ` and is cashed in here against the run whose branch selection
--     depends on it. Vacuous at `Γ.natPeano = false`, hence the machine-mode bridge
--     theorem is EXACTLY as strong as before. It is a side condition on the parameter
--     `Γ` (like S2's `knames` and W3.1's fixvar agreement), NOT a trust assumption:
--     the construction sites (`gBridgeInv_nil`, the three in-file guards) take it as an
--     explicit hypothesis and every existing caller discharges it by `simp`.
--
--   * motive 2 (`visitLiteral`) went from `True` to content, and motive 3
--     (`visitConstructor`) relaxed `cn ≠ Nat.zero → cn ≠ Nat.succ` to the disjunction
--     `ctx.config.nat = .peano ∨ (cn ≠ Nat.zero ∧ cn ≠ Nat.succ)`. The relaxation only
--     ADMITS more calls (under peano the machine-`Nat` arms of `visitConstructor` are
--     dead for every `cn`); `Supported.ctorApp` is NOT relaxed, so motives 13/14 keep
--     their disequalities and pass the right disjunct.
--
-- Expectation: no axiom of ours, and no movement. The literal path introduces no new
-- primitive and no new trust clause — `visitLiteral` calls `visitConstructor`, whose
-- `DataBridgeHyps` clauses are keyed on `Γ.ctors` and hence already cover `Nat.zero` /
-- `Nat.succ` (both are non-`@[extern]` in the real kernel, and the argmask slice is
-- trivial at `numParams = 0`, `numFields ∈ {0,1}`). The recursion
-- `visitLiteral → visitConstructor → visitAppArgs → visitExpr → visitLiteral` is carried
-- by the fixpoint induction itself, so no measure and no new admissibility obligation.
-- ============================================================================

#print axioms LeanToLambdaBox.Supported.instantiate1'
#print axioms LeanToLambdaBox.Supported.instantiate1
#print axioms LeanToLambdaBox.BridgeInv
#print axioms LeanToLambdaBox.BridgeInv.mono
#print axioms LeanToLambdaBox.BridgeInv.mono_state
#print axioms LeanToLambdaBox.BridgeInv.mkLocalDecl
#print axioms LeanToLambdaBox.BridgeInv.mkLetDecl
#print axioms LeanToLambdaBox.visitExpr_refines_erases_core
#print axioms LeanToLambdaBox.visitExpr_refines_erases
#print axioms LeanToLambdaBox.gBridgeInv_nil
-- The capstones: statements unchanged, so their sets must be unchanged too.
#print axioms LeanToLambdaBox.shipping_visitExpr_correct
#print axioms LeanToLambdaBox.shipping_visitExpr_correct_data
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_registered

-- ============================================================================
-- The Nat-literals wall, slice L4 (2026-08-12): capstones and the end-to-end guard.
--
-- CAPSTONE RIPPLE: none at the statement level. Every capstone
-- (`shipping_visitExpr_correct{,_data}`, `shipping_erase_correct_firstorder{,ι}` and the
-- `_registered` forms) takes `BridgeInv` as a PREMISE, so the new `natcfg` field costs
-- them nothing; only the places that *build* an invariant gained the side condition
-- `Γ.natPeano = true → cfg.nat = .peano` — `gBridgeInv_nil` and the five guards. That is
-- the same shape as S2's `hkn` and W3.1's `hnfv`, and every existing caller discharges it
-- by `simp` (their `Γ`s leave `natPeano` at its `false` default).
--
-- THE END-TO-END GUARD: D3 (`shipping_erase_correct_firstorder`) fires on the raw
-- literal node `2` in peano mode. What the wall contributes is constructed, not assumed:
--
--   * `envNatT` — `Nat : Sort 1`, `Nat.zero : Nat`, `Nat.succ : Nat → Nat` as typed
--     axioms (`envNatT_wf`), the smallest `VEnv` in which a literal's own `TrExprS`
--     witness exists: lean4lean translates `.lit l` THROUGH `Literal.toConstructor`, so
--     the witness is a `Nat.succ` spine and needs the constructors declared and typed.
--     `envNatLit` (L1) only declares `Nat`, which is all `ContainsLits` needs.
--   * `trExprS_natLit` / `trExprS_srcNatTower` — the literal and its value land on the
--     SAME `vNatTower n`. That is lean4lean's own literal rule, and it is why subject
--     reduction for literals was free in L2.
--   * `sevalDataC_natLit`, `erasesEnvCtor_natLit`, `firstOrderValue_srcNatTower`.
--
-- Hypothetical, per precedent: the run, the three trust bundles, `NoBlock t`, and the
-- single lean4lean-blocked arity side condition `harity` — the very one `FirstOrder.lean`
-- carries for `envFO` (`.const`-vs-arity defeq injectivity is not exposed by the pin).
--
-- SCOPE, stated so it is not over-read: this is the `Expr.lit` node. A source-level
-- numeral `(5 : Nat)` is `@OfNat.ofNat Nat (lit 5) (instOfNatNat (lit 5))`, whose
-- `OfNat.ofNat` body erases to an `LBTerm.proj`; `Erases` is projection-free by design,
-- so a user-written numeral still does not δ-unfold in the model. `Nat.add` is
-- `@[extern]`, hence an axiom under the shipping default. Neither is touched by this
-- wall. [2026-08-27: the parenthetical used to read "(lean4lean's `TrProj` is a
-- `sorry`)", i.e. it gave the UPSTREAM gap as the reason `Erases` has no projection rule.
-- That reason is gone — A1 gave `TrProj` a real definition, so an `Erases.proj` rule is
-- now WRITABLE. The restriction that survives is ours and is downstream work: `Supported`
-- has no `.proj` rule (`Bridge.lean`), and `NoProj` is what the `box` arm of the
-- uniformity argument pays for. The scope statement above is still correct; only its
-- justification changed.]
--
-- Expectation: no axiom of ours; `envNatT_wf` and the typing lemmas carry lean4lean's
-- `VEnv.WF` machinery exactly as `envFO_wf` does.
-- ============================================================================

#print axioms LeanToLambdaBox.envNatT_wf
#print axioms LeanToLambdaBox.envNatT_towerType
#print axioms LeanToLambdaBox.trExprS_natLit
#print axioms LeanToLambdaBox.trExprS_srcNatTower
#print axioms LeanToLambdaBox.sevalDataC_natLit
#print axioms LeanToLambdaBox.envNatT_natNotProp
#print axioms LeanToLambdaBox.informativeType_srcNatTower
#print axioms LeanToLambdaBox.firstOrderValue_srcNatTower

-- ----------------------------------------------------------------------------
-- L3 + L4 axiom movement: MEASURED, not asserted. This file was run at `3d67f2a`
-- (the pre-L3 tip) and at the L4 tip, and the two outputs compared declaration by
-- declaration: **337 declarations in the baseline, 0 changed, 0 removed.** The nine
-- additions are the new declarations themselves — `envNatT_wf`, `envNatT_towerType`,
-- `trExprS_natLit`, `trExprS_srcNatTower`, `sevalDataC_natLit`, `envNatT_natNotProp`,
-- `informativeType_srcNatTower`, `firstOrderValue_srcNatTower` — plus `BridgeInv.mono`,
-- which was newly *printed* here, not newly introduced. `envNatT_wf` and
-- `sevalDataC_natLit` are `sorryAx`-free; the rest carry the `TrExprS` boundary their
-- neighbours already carried.
-- ----------------------------------------------------------------------------

-- ============================================================================
-- The DAG cold-start wall, slice S3 (2026-08-12): the entry point and the
-- registration exits, decomposed — and the δ half composed OUTSIDE the inductions.
--
-- WHY OUTSIDE. The shape half (S1d) travels as a state predicate `Q : ErasureState →
-- Prop`; a state predicate has no room to mention the `visitExpr` run whose OUTPUT is
-- being stored, so it cannot carry an `Erases` witness for it. Widening it is not
-- available either: inside `visitExpr.mutual_fixpoint_induct` the step goal for
-- `visitMutual` sees the fixpoint's ABSTRACT erasure argument. And the bridge induction
-- cannot host the content — that is S2's recorded finding (motive 6 stays `True`). So the
-- δ content is composed about the REAL functions, from `run_visitMutual_decomp`.
--
-- WHAT IS PROVED FROM THE RUN: the entry point reduces to `prepare_erasure` + `visitExpr`
-- from the EMPTY state (R1); `prepare_erasure` is state-transparent with csimp off (R2),
-- which is what pins that state to `{}`; the non-recursive exit's stored body is found by
-- `envLookup` under `Γ.constants n` and really erases the body the run erased; the
-- recursive block's siblings are each found at their own index.
--
-- LEDGER: one trust item LEAVES. `PrepareHyps.prepare_sound` was a fourth, independent
-- field of the trust class; it is now the THEOREM `prepare_sound_of_prepareHyps`, derived
-- from the three per-transform fields along R2's monadic-bind decomposition. Nothing is
-- added: the residues (context-uniformity of a constant body's erasure, the applied form
-- of the stored body, the `Esrc`-domain agreement, and the recursive block's δ witness)
-- are explicit named premises of the walk step, not new bundles.
--
-- Expectation: the pure `EraseM`/`CoreM`/`LBTerm` layer is sorryAx-free (R1, R2, the
-- decomposition, the `Kername.beq` and `envLookup` kit, the recursive registration and
-- its guard); the two bridge-facing results carry exactly the lean4lean boundary
-- `erases_nonrec_const_body` already carried.
-- ============================================================================

#print axioms LeanToLambdaBox.Kername.eq_of_beq
#print axioms LeanToLambdaBox.InlineExt.runConcl
#print axioms LeanToLambdaBox.run_nonrec_exit_decomp
#print axioms LeanToLambdaBox.run_rec_exit_decomp
#print axioms LeanToLambdaBox.run_visitMutual_decomp
#print axioms LeanToLambdaBox.run_prepare_erasure_ok
#print axioms LeanToLambdaBox.prepare_sound_of_prepareHyps
#print axioms LeanToLambdaBox.erase_run_ok
#print axioms LeanToLambdaBox.envLookup_of_mem_of_keys
#print axioms LeanToLambdaBox.envLookup_mono_of_keys
#print axioms LeanToLambdaBox.erases_nonrec_const_registered
#print axioms LeanToLambdaBox.recConstState_envLookup
#print axioms LeanToLambdaBox.registeredClosureData_step_nonrec
#print axioms LeanToLambdaBox.RegisteredClosureData.mono
#print axioms LeanToLambdaBox.gRecConstState_lookups
#print axioms LeanToLambdaBox.gRecConstState_no_shadow

-- ============================================================================
-- The DAG cold-start wall, slice S4 (2026-08-12): the capstone's subject becomes
-- `Erasure.erase`.
--
-- THE STATEMENT. `Erasure.erase e cfg cctx ref w = .ok (p, inls) w'` from the EMPTY state
-- now yields `∃ E t t', p = .untyped E (some t) ∧ WcbvEval E appliedFlags t t' ∧ … ∧
-- (uniqueness)`. `E` and `t` are PRODUCED, not consumed. Discharged from the run: the
-- state (R1+R2 — csimp off makes `prepare_erasure` state-transparent, so the `visitExpr`
-- run really starts at `{}`), the environment, `ClosedEnv E`, `LBClosed t 0` (R11, no
-- hypotheses), the bridge invariant (CONSTRUCTED at `{}` by `gBridgeInv_nil`), and the
-- three registration records (from `RegInvShape`, modulo registration completeness).
--
-- A REFUTED PREMISE, RAISED NOT INHERITED. Slice S1d's `RegShapeHyps` is INCONSISTENT,
-- so its corollaries `visitExpr_regInvShape` / `visitMutual_regInvShape` /
-- `get_constant_kername_regInvShape` are vacuous. Two independent proofs land here:
--   * `regShapeHyps_fresh_refuted` — `fresh` quantifies over EVERY state satisfying the
--     invariant with no link to the call; at `addAxiomState n {}` (a state S1's own
--     `RegInvShape.addAxiom` produces) it asserts `Kername.beq (toKername n) (toKername n)
--     = false`;
--   * `regShapeHyps_recClosed_refuted` — `recClosed` asserts `LBClosed (.fix defs j) 0`
--     for EVERY block, including a one-definition block whose body is `.bvar 5`.
-- `regKeys`/`regCtors`/`regCases`/`regFields` fall the same way (the `register_inductive`
-- HIT run is constructible, so they can be instantiated at a hand-made empty-`gdecls`
-- state). The repair is stated at the refutation: a coverage field in `RegInvShape` (which
-- needs R4's `ConstExt` to record its axiom prefix's KEYS) plus a `RunClosed.rc` that
-- TAKES the block's closedness — both inside S1's files, but together a re-run of the
-- 18-motive shape induction, hence a slice of their own. Until then the capstone routes
-- the preservation through `RegBridgeHyps.regInv`, which is keyed on an actual run and so
-- sits in the epistemic class of `BridgeHyps` (no run of the family is constructible
-- in-logic): not decidable here, not refutable here.
--
-- [S1e, below] Both moving parts landed and the diagnosis was sharpened: coverage does not
-- restore key DISTINCTNESS, and nothing can — `runClosed_keysDistinct_refuted`. The
-- capstones now route the preservation through the THEOREM `visitExpr_regInvShape`, and
-- `RegBridgeHyps.regInv` is gone.
--
-- SCOPE, so it is not over-read. `BridgeInv.known_dom` says a `known` constant is ALREADY
-- registered; at `{}` nothing is, so `known = ⊥` and `Supported.const` is unusable. The
-- cold-start fragment therefore contains NO δ-constant, and `Esrc` is empty: the δ records
-- are discharged vacuously, not from the walk. Closing that needs bridge motive 5's miss
-- branch, which needs motive 6 to conclude an UNCONDITIONAL state/generator fact — and
-- motive 1's conclusion is entirely conditional, so it is a restructuring of
-- `visitExpr_refines_erases_core`, not a new `RegBridgeHyps` field as S2's note supposed.
--
-- Expectation: the two capstones' axiom sets are IDENTICAL to
-- `shipping_erase_correct_firstorder{,ι}_registered`'s — no axiom of ours, no movement.
-- The two refutations are pure `LBTerm`/state reasoning and are sorryAx-free.
-- ============================================================================

#print axioms LeanToLambdaBox.regShapeHyps_fresh_refuted
#print axioms LeanToLambdaBox.regShapeHyps_recClosed_refuted
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart

-- ============================================================================
-- COLD-START SLICE S1e (2026-08-12): the refuted `RegShapeHyps` bundle, repaired.
--
-- Same expectation as S1/S1d: this layer is pure `LBTerm`/`EraseM`/`GlobalDeclarations`
-- reasoning — no `Erases`, no `TrExprS`, no lean4lean — so ⊆ [propext, Classical.choice,
-- Quot.sound] and NO `sorryAx`, tight rather than inherited. The two capstones'
-- sets must not move at all.
--
-- WHAT WAS WRONG, AND HOW FAR DOWN. S4 refuted two fields of S1d's `RegShapeHyps`. The
-- defect is one level deeper: with `keys : KeysDistinct s.gdecls` in `RegInvShape`, the
-- statement `RunClosed (RegInvShape Γ)` is ITSELF false, at every `Γ`. `RunClosed.nrc` is
-- a bare STATE closure — it is applied inside `run_nonrec_exit_ok` at whatever state the
-- body's erasure left behind, with no run in scope — so it must survive two conses at the
-- same name, which duplicate a key. `runClosed_keysDistinct_refuted` proves it in five
-- lines and needs no hypothesis on `Γ` at all. No repair of the HYPOTHESES existed.
--
-- THE REPAIR.
--   * `RegInvShape` trades `keys` for `cover : ConstKeysCovered s` — every `.constantDecl`
--     entry is filed under the canonical kername of a constant the registry knows. Every
--     registration site preserves it with NO side condition, which is why every freshness
--     premise disappears from the S1 step lemmas (`addAxiom`, `constCons`, `constExt`,
--     `registerInd`, `recConst` and the two `…_run` forms all lost theirs). What coverage
--     buys back is `RegInvShape.fresh_of_unregistered`: an unregistered name owns no
--     constant key — the freshness the design called `hkinj`, now DERIVED at the one guard
--     the code really tests (`get_constant_kername`'s miss branch), modulo injectivity of
--     `toKername`, which is a naming assumption and not a theorem.
--   * `Erasure.ConstExt` now records the KEYS of its axiom prefix, not just its shape —
--     without that, coverage cannot cross a `register_inductive` call, whose cold branch
--     emits one `addAxiom` per `@[extern]` constructor. This is R4's contribution to S1e.
--   * `RunClosed.rc` TAKES `∀ j, LBClosed (.fix defs j) 0`. `Erasure.run_rec_exit_ok` now
--     reports the shape of the block it is storing (`defs.length = names.length`, and per
--     definition "my body is a `mkDef` closure of a `Cl` erasure output over `fixnames`"),
--     from which `rec_block_closed` computes the closedness inside the induction.
--     S1d's `recClosed`, refuted at `.fix [{body := .bvar 5}] 0`, is gone.
--   * The premise record is now `RegBridgeHyps`, merging what survived of `RegShapeHyps`
--     (`knames`, `prep`, the three `Γ`-agreement fields) with S4's own bundle (`satCtors`,
--     `satCases`). S4's `regInv` field is the THEOREM `visitExpr_regInvShape`.
--   * The `Γ`-agreement fields are now guarded by the cold branch's own test
--     (`s.inductives.get? ii.name = none`). That guard is load-bearing, and S1e formalises
--     why: `Erasure.run_register_inductive_hit_mk` CONSTRUCTS a hit-branch run out of
--     `get`/`pure`, so `regShapeHyps_regCtors_refuted` instantiates S1d's unguarded field
--     at a hand-made state with empty `gdecls` — at a `Γ` that records a constructor, i.e.
--     at exactly the `Γ` the capstone is interesting at. Cold runs are not constructible
--     (their body reads the environment through `getConstInfo`), so the guarded field is
--     in the epistemic class of `BridgeHyps`.
--
-- WHAT THE INVARIANT NO LONGER CLAIMS. Key distinctness of `gdecls` is not an invariant of
-- the shipping walk, and `ColdStartDelta`'s `KeysDistinct` premises stay premises of their
-- callers. Two independent reasons, both recorded in code: the `nrc` refutation above, and
-- `addAxiom`'s panic fall-through (its "already defined" guard has no `return`, so a
-- second entry under the same key is consed). A third, orthogonal fact was found while
-- stating coverage: `mutualBlockKn_eq_toKername` — the block keys are INSIDE the constant
-- keys (`rootKername s` IS `toKername (.str .anonymous s)`), so for a root-level single
-- inductive `A` the block entry and an axiom entry for `A` collide, first-match-wins.
-- Whether that is reachable is a question about the shipping eraser (it needs a bare
-- inductive constant to pass the erasability gate into `visitMutual`), NOT about this
-- development; it is raised, not patched.
--
-- Expectation: no axiom of ours, no movement in the capstones, no `sorryAx` anywhere in
-- this block.
--
-- ONE MOVEMENT, AND ITS CAUSE. Six entries in the S1 block above gained
-- `Classical.choice`: `RegInvShape.registeredCtors`/`registeredCases`/
-- `registeredCtorFieldsAll`/`noFixEnv`/`closedEnv`/`inlinings`, all of which were
-- `[propext, Quot.sound]`. Nothing about them changed; the INVARIANT they project from
-- did. Its old `keys` field was `List.Pairwise` on kernames, which mentions no shipping
-- function, while `cover` mentions `Erasure.toKername` — and `toKername`, through
-- `cleanIdent`'s string walk, carries `Classical.choice`, exactly as every other
-- `toKername`-mentioning entry in the S1 block already did (`RegInvShape.empty`,
-- `addAxiom_run`, `nonrecConst`, …). Additions only, inside the allowed set, and no
-- `sorryAx` reach anywhere.
-- ============================================================================

-- The strengthened `ConstExt` and the constructible hit run.
#print axioms Erasure.ConstExt.trans
#print axioms Erasure.AxiomExt.addAxiom
#print axioms Erasure.run_register_inductive_hit_mk
#print axioms Erasure.run_rec_exit_ok
#print axioms Erasure.run_visitMutual_ok

-- Coverage: the invariant's new field, its preservation, its payoff, and the key-space
-- overlap that scopes it.
#print axioms LeanToLambdaBox.ConstKeysCovered.cons
#print axioms LeanToLambdaBox.RegInvShape.empty
#print axioms LeanToLambdaBox.RegInvShape.addAxiom
#print axioms LeanToLambdaBox.RegInvShape.constExt
#print axioms LeanToLambdaBox.RegInvShape.registerInd
#print axioms LeanToLambdaBox.RegInvShape.constCons
#print axioms LeanToLambdaBox.RegInvShape.recConst
#print axioms LeanToLambdaBox.RegInvShape.addAxiom_run
#print axioms LeanToLambdaBox.RegInvShape.register_inductive_run
#print axioms LeanToLambdaBox.RegInvShape.fresh_of_unregistered
#print axioms LeanToLambdaBox.rootKername_eq_toKername
#print axioms LeanToLambdaBox.mutualBlockKn_eq_toKername
#print axioms LeanToLambdaBox.gRegInvShape_addAxiom
#print axioms LeanToLambdaBox.gRegInvShape_addAxiom₂
#print axioms LeanToLambdaBox.gRegInvShape_fresh

-- The block's own closedness, supplied instead of assumed.
#print axioms LeanToLambdaBox.lbClosed_foldl_zipIdx_map
#print axioms LeanToLambdaBox.lbClosed_fix_of_bodies
#print axioms LeanToLambdaBox.rec_block_closed

-- The re-run induction and the de-vacuized corollaries.
#print axioms LeanToLambdaBox.visitExpr_shape
#print axioms LeanToLambdaBox.runClosed_true
#print axioms LeanToLambdaBox.visitExpr_noFix_closed
#print axioms LeanToLambdaBox.RunClosed.regInvShape
#print axioms LeanToLambdaBox.visitExpr_regInvShape
#print axioms LeanToLambdaBox.visitMutual_regInvShape
#print axioms LeanToLambdaBox.get_constant_kername_regInvShape

-- The guards: the negative one that forced the design, and the positive one that shows
-- the repaired bundle is inhabited and its corollaries fire.
#print axioms LeanToLambdaBox.runClosed_keysDistinct_refuted
#print axioms LeanToLambdaBox.gRegBridgeHyps
#print axioms LeanToLambdaBox.gVisitExpr_regInvShape

-- The third refutation of the superseded record (the one S4 asserted but did not prove).
#print axioms LeanToLambdaBox.regShapeHyps_regCtors_refuted

-- ============================================================================
-- δ-inclusion, slices D1-D3 (2026-08-12): the walk hands back the declaration it
-- fetched, the registration exits get world-indexed twins, and the δ SCOPE bundle
-- lands beside the three trust bundles.
--
-- THE WALL, RESTATED. A cold start begins at the empty state, so `BridgeInv.known_dom`
-- ("a `known` constant is already registered") is not merely strong there — it is FALSE
-- for every non-empty fragment (`old_known_dom_cold_refuted`, kept below). That is what
-- pinned every cold-start capstone to `known = ⊥`, and `Supported.const` needs `known n`,
-- so a cold-started program could not CALL anything. Slice D4a removes the wall.
--
-- WHAT LANDED.
--   * D1 — `run_visitMutual_decomp` now hands back the `getDeclInfo?` run itself (at the
--     `CoreM` layer), the `prepare_erasure` run, the dependency's reader context pinned to
--     `{ ctx with fixvars := none, lparams := ci.levelParams }`, and the entry-side
--     `InlineExt`. All four facts were already in the proof and were discarded; the
--     declaration is what every branch condition (`isExtern`, `getInlineAttribute?`,
--     `name_occurs`, `value?`) is a pure function of, so pinning it is what separates the
--     three disjuncts. Axiom set UNCHANGED (`[propext, Classical.choice, Quot.sound]`).
--   * D2 — `run_{inline_tail,inline_prefix,nonrec_exit,rec_exit}_ok'`, the same four
--     registration rules over `P : ErasureState → Void IO.RealWorld → Prop` instead of
--     `Q : ErasureState → Prop`. Two forced differences: every state-transparent primitive
--     on the path (`logInfo`, `Meta.isInstance`, `mkFreshFVarId`, `getConstInfo`) advances
--     the world and so needs its own clause — free in the state-only form — and `hvE` is
--     keyed on the `prepare_erasure` run as well, so a caller can RE-ESTABLISH an
--     invariant at the erasure's entry state rather than merely propagate one. Pure
--     `EraseM` reasoning: all four are sorryAx-free.
--   * D3 — `DeltaHyps`, the scope-side half of the contract whose state-side half is
--     `BridgeInv`: fragment δ-closure (`esrc_sub`/`disj`), the decl-fetch/`Esrc` agreement
--     (`decl_run`), prepared dependency bodies `Supported` + translatable (`prepared`),
--     `axiom_free`, `nofixvars`, the five generator-bookkeeping clauses, and the `∀ Δ`
--     uniformity residue. Epistemic class: `BridgeHyps`/`RegBridgeHyps` — Hoare specs for
--     REAL calls (none of the primitives is in the `visitExpr` mutual block), never an
--     axiom, never a statement about a whole environment.
--
-- LEDGER: additions only, and no NEW kind of trust. `DeltaHyps` is a `Prop` bundle, so it
-- is a hypothesis, never an axiom; unlike `CasesBridgeHyps` it is `env`/`Us`-indexed
-- (`prepared` mentions `TrExprS`, `uniform` mentions `Erases`), so its TYPE carries
-- lean4lean's `sorryAx` exactly as `BridgeInv`'s does. Nothing moved: no existing entry's
-- axiom set changed, and `run_visitMutual_decomp` in particular is byte-identical in its
-- ledger row after the widening.
--
-- WHAT DID **NOT** LAND IN D3, AND WHY. The design's D3 also called for DELETING
-- `BridgeInv.known_dom` with the promise "green after this slice". That is not achievable
-- as a separate slice, and the two guards below are the proof:
--   * `old_known_dom_cold_refuted` — the field is refutable at the entry configuration,
--     so it does have to go (the design's diagnosis is right);
--   * `constants_get!_unregistered_ne` — but it is the ONLY thing forcing motive 5's hit
--     branch, and the miss branch returns `s'.constants[n]!`, i.e. `default`, which is not
--     `Γ.constants n`. Discharging the miss branch needs "`visitMutual n` registered `n`",
--     which inside `visitExpr.mutual_fixpoint_induct` can only come from motive 6 — before
--     D4a, `True`. Giving motive 6 content is a statement change to the crown theorem
--     (it must then take `DeltaHyps`, which is NOT vacuous at `known = ⊥` because of the
--     bookkeeping clauses, hence a new premise at every consumer). So the field's death
--     and motive 6's content are one atomic change — slice D4a, below.
-- ============================================================================

-- D1: the widened decomposition (ledger row unchanged).
#print axioms LeanToLambdaBox.run_visitMutual_decomp

-- D2: the world-indexed twins of the registration exits.
#print axioms Erasure.run_inline_tail_ok'
#print axioms Erasure.run_inline_prefix_ok'
#print axioms Erasure.run_nonrec_exit_ok'
#print axioms Erasure.run_rec_exit_ok'

-- D3: the scope bundle and its non-vacuity at a genuinely non-empty fragment.
#print axioms LeanToLambdaBox.DeltaHyps
#print axioms LeanToLambdaBox.gDeltaFragment_nonempty
#print axioms LeanToLambdaBox.gDeltaScope
#print axioms LeanToLambdaBox.gDeltaSupported

-- D3: the two negative guards that scope the `known_dom` deletion.
#print axioms LeanToLambdaBox.constants_get!_unregistered_ne
#print axioms LeanToLambdaBox.old_known_dom_cold_refuted

-- ============================================================================
-- δ-inclusion, slice D4a (2026-08-12): `BridgeInv.known_dom` is DELETED, `visitMutual`'s
-- motive gets content, and `get_constant_kername`'s miss branch closes. A cold-started
-- program may now CALL a constant.
--
-- WHAT LANDED, in one atomic change (the field's death and the motive's content are not
-- separable — see the D3 note above):
--   * `BridgeInv` loses `known_dom` (field + 4 transports + 7 vacuous construction sites);
--     the invariant no longer mentions `known` at all, and `bridgeInv_cold_known` shows it
--     is now SATISFIABLE at the entry configuration for a non-empty fragment — the exact
--     statement that was refutable before (`old_known_dom_cold_refuted`, kept).
--   * motive 6 (`visitMutual`) stops being `True`: under `BridgeInv` + `known n` a
--     successful call now concludes `RunConcl s s' ∧ gw w ≤ gw w' ∧ (s'.constants.get? n).isSome`
--     — the same CONDITIONAL shape motive 5 has. Step 6 is proved by walking the four
--     exits (`@[inline]` prefix, the two `addAxiom` exits, the non-recursive exit; the
--     recursive exit is refuted inside the fragment by `DeltaHyps.decl_run`'s
--     `name_occurs`), rebuilding `BridgeInv` field-by-field at the dependency's reader —
--     `withReader` moves only `fixvars` (matched by `DeltaHyps.nofixvars`) and `lparams`
--     (pinned at `Us` by `decl_run`) — and feeding motive 1's OWN IH with the fragment's
--     `Supported`/`TrExprS` (`DeltaHyps.prepared`).
--   * motive 5's miss branch is proved, not refuted: `hashMap_get!_of_get?` makes the
--     `panic!`-defaulting lookup total from the registration conclusion, and
--     `RunConcl.canon` makes it canonical at the POST-state (where `BridgeInv.consts` no
--     longer applies) — the same move `BridgeInv.mono_state` makes.
--   * `visitExpr_refines_erases{,_core}` take `DeltaHyps` (∀ `cctx`/`ref`, since those are
--     bound inside the conclusion), threaded opaquely through every consumer:
--     `erases_nonrec_const_body`, `shipping_visitExpr_correct{,'}`,
--     `shipping_visitExpr_correct_data`, `shipping_erase_correct_firstorder{,_registered}`,
--     `shipping_erase_correct_firstorderι{,_of_shape,_registered}`,
--     `erases_nonrec_const_registered`, `registeredClosureData_step_nonrec`, and the two
--     cold-start capstones.
--
-- TWO CLAUSES THE BUNDLE WAS SHORT, both forced by the point of use and both recorded at
-- their fields (this is a STRENGTHENING of a hypothesis, so it is stated, not buried):
--   * `prep_esrc` — `prepared` is keyed on `Esrc n = some pe` at the run's own output,
--     while `decl_run` only gives `(Esrc n).isSome`; the two cannot be joined in-logic
--     (one names *some* body, the other produces *its* body). `prep_esrc` states the
--     identification, keyed on the two runs a caller inside the induction holds. It is the
--     same fact `registeredClosureData_step_nonrec` takes as `hEsrc` at the composition
--     site; there is no composition site inside an induction.
--   * `prep_run` gains `s' = s`. `prepare_erasure`'s state transparency is PROVED for
--     csimp-off configurations (`run_prepare_erasure_state`), but the reader's config is
--     an induction variable and `BridgeInv` does not pin `csimp`, so the gate is invisible
--     at the point of use. Same classification as `Erasure.run_nonrec_exit_ok`'s `hprep`,
--     whose docstring already says so.
--
-- LEDGER: no new axiom, no `sorry`. Deleting an invariant field WEAKENS every theorem's
-- premise; adding two bundle clauses strengthens `DeltaHyps`, which is a `Prop` premise,
-- never an axiom. The bridge's own axiom row is unchanged.
-- ============================================================================

-- The crown theorem and its core, after the deletion + the new premise.
#print axioms LeanToLambdaBox.visitExpr_refines_erases_core
#print axioms LeanToLambdaBox.visitExpr_refines_erases

-- The invariant is satisfiable at a NON-EMPTY fragment at the cold-start entry state
-- (this is the wall, gone), and the deleted field's statement is still refutable there.
#print axioms LeanToLambdaBox.bridgeInv_cold_known
#print axioms LeanToLambdaBox.old_known_dom_cold_refuted

-- The two small totality lemmas the miss branch needs.
#print axioms LeanToLambdaBox.hashMap_get!_of_get?
#print axioms LeanToLambdaBox.constantInfo_value!_of_value?

-- The registration deltas the new motive reports, as `RunConcl` steps.
#print axioms Erasure.run_inline_prefix_decomp'
#print axioms Erasure.runConcl_nonrecConstState
#print axioms Erasure.runConcl_addAxiomState
#print axioms Erasure.nonrecConstState_get?

-- What the empty fragment still buys (the bookkeeping half, spelled out).
#print axioms LeanToLambdaBox.DeltaHyps.of_bot

-- The consumers, threaded: the capstones' axiom sets must be UNCHANGED.
#print axioms LeanToLambdaBox.shipping_visitExpr_correct
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart

-- ============================================================================
-- δ-inclusion, slice D4b (2026-08-12): the δ RECORD travels the walk. Every bridge
-- motive's state conclusion is now `RunConclδ` — `Erasure.RunConcl` plus "the record
-- survived" — so the top-level run reports what the walk recorded, instead of the
-- capstone assuming it.
--
-- WHAT LANDED.
--   * `DeltaMem` — "every constant body the walk RECORDED for a fragment name erases the
--     source body `Esrc` records for it", membership-flavoured (S1e proved no state
--     predicate along the walk can maintain `KeysDistinct`, so `envLookup` cannot be the
--     carrier; the conversion happens once, at the end).
--   * `RunConclδ` — the bundle that made the threading cheap: `rc` + the record's
--     transport, produced and composed exactly where a `RunConcl` was, so the ~40
--     conclusion sites of the 18-motive induction did not have to change shape.
--   * step 6 extends the record at the non-recursive exit (the body it just erased, from
--     motive 1's own IH), and transports it across the axiom exits and the `@[inline]`
--     bookkeeping for free; step 3 and step 17 transport it across `register_inductive`
--     via `run_register_inductive_gdeclsConst` — every entry that call conses is an
--     `.inductiveDecl` or a value-less `.constantDecl ⟨none⟩`.
--   * `registeredClosure{,Data}_of_deltaMem` — the capstone-side conversion (membership
--     + `KeysDistinct` → `envLookup`). D5 wires it up; it is not wired here.
--
-- FOUR DESIGN CLAIMS THAT DID NOT SURVIVE CONTACT, all recorded at their definitions:
--   1. the record cannot be keyed on the registry DOMAIN (the design's shape). The domain
--      grows at `register_inductive`'s `@[extern]`-constructor `addAxiom` prefix, and
--      `run_register_inductive_cold_ok` exposes a `ConstExt`, not the per-name `addAxiom`
--      runs `DeltaHyps.axiom_free` would need. Keyed on the recorded ENTRY, the same call
--      transports for free — at the price of the existence half becoming a premise of the
--      conversion (`hreg`).
--   2. `NoBlock` cannot be part of the record: it is an output-shape statement, the shape
--      induction proves `NoFix`/`LBClosed` and not it, and inside the bridge the erasure
--      argument is abstract. It is a premise of the `Data` conversion.
--   3. `∀ Δ` cannot be part of the record either: the bridge fires at the `Δ` of the CALL
--      SITE (`visitMutual`'s `withReader` keeps the ambient `lctx`), so the record carries
--      `∃ Δ` and the conversion takes the `huni` residue this development already carries
--      everywhere else.
--   4. the extension step is FALSE without a naming assumption: `Erasure.toKername` is not
--      injective (`mutualBlockKn_eq_toKername`), so two names can share a `gdecls` key and
--      the record is then false for one of them. `DeltaHyps.kinj` restricts it to the
--      fragment — the fragment-scoped form of the capstone's `hkinj`.
--
-- LEDGER: no new axiom. `DeltaMem`/`RunConclδ` are `Prop`s over `Erases`, so their types
-- carry lean4lean's `sorryAx` exactly as `BridgeInv`'s do; the two `Erasure`-side lemmas
-- are pure `EraseM`/list reasoning and are sorryAx-free.
-- ============================================================================

#print axioms LeanToLambdaBox.DeltaMem
#print axioms LeanToLambdaBox.DeltaMem.empty
#print axioms LeanToLambdaBox.DeltaMem.nonrec
#print axioms LeanToLambdaBox.RunConclδ
#print axioms LeanToLambdaBox.RunConclδ.trans
#print axioms Erasure.run_register_inductive_gdeclsConst

-- The record is non-vacuous on real data, and converts.
#print axioms LeanToLambdaBox.gDeltaMem
#print axioms LeanToLambdaBox.registeredClosure_of_deltaMem
#print axioms LeanToLambdaBox.registeredClosureData_of_deltaMem

-- ============================================================================
-- δ-inclusion, slice D5 (2026-08-12): the cold-start capstones are rewired for δ. A
-- cold-started program may now CALL a walked function, and the capstone PROVES the
-- environment fact that makes the target's δ step legal instead of assuming it.
--
-- WHAT LANDED.
--   * `known` and `Esrc` are PARAMETERS of both capstones. `gBridgeInv_nil` gained a
--     `known` argument (the invariant stopped mentioning `known` at D4a; this was the last
--     place the entry configuration pinned the fragment at `⊥`), and `ColdStartSubject`
--     gained a `known` index so the subject may reference constants.
--   * `ErasesEnvDeltaData` is DERIVED: the bridge's `RunConclδ` carries `DeltaMem.empty`
--     from the entry state to the run's final state, and
--     `registeredClosureData_of_deltaMem_walked` converts membership to `envLookup`.
--   * `SEnv.walked` — `Esrc` cut to the constants the final environment stores a BODY for,
--     keyed on `LBTerm.envLookup` (the target semantics' own δ-lookup). The capstones'
--     source-evaluation premise is stated at that restriction.
--   * `NoBlockEnv` + `ColdStartSubject.noBlockEnv`; `SEnvConsistent.walked`;
--     `DeltaHyps.uniform` generalised from `Δ = []` to two arbitrary contexts (`DeltaMem`
--     carries `∃ Δ`, the CALL SITE's, so nothing one-sided bridges it).
--   * The `Hδ` bundle's `Esrc` is SPLIT from the simulation's in every shipping theorem
--     (`Esrcδ`): the bundle's is the fragment (a scope), the simulation's is what the
--     evaluation δ-unfolds (the walk-restricted one). Conflating them forces either a false
--     record or a bundle at an environment `DeltaHyps.prep_esrc` cannot be stated at.
--
-- THE FOUR OPEN PREMISES OF THE D4b CONVERSION, RESOLVED:
--   * existence (`hreg`) — **DERIVED**. `SEnv.walked`'s defining condition *is* the lookup
--     the record needs. It does NOT fall to `RegInvShape.cover`, which states the converse
--     (every stored constant key is a name the registry knows), and it is not provable in
--     the unrestricted form at all: a fragment constant the program never mentions is never
--     registered, so unrestricted `ErasesEnvDeltaData` is FALSE, not merely unproved.
--   * key distinctness (`hkeys`/`hkinj`) — **ELIMINATED**. Keyed on `envLookup` rather than
--     on membership, the conversion never turns a membership into a lookup. This is one
--     premise better than the design predicted (it expected `hkinj` to be paid here).
--   * context-uniformity (`huni`) — **DISCHARGED at slice δ-D7b**. `DeltaHyps.uniform` is
--     deleted; the capstones call `ErasesUniform.erases_uniform_closed`. The context it
--     starts from comes with its own well-formedness and `NoBV` (δ-D7b(i)), both free at
--     the production site (`BridgeInv.vlctx_wf`/`BridgeInv.noBV`) and recoverable nowhere
--     else. What is left is ONE named VExpr-level premise, `ErasableStrengthen`.
--   * applied form (`hnb`) — **RETIRED at slice δ-N**, and the claim recorded here was
--     wrong. `NoBlock` is `True` on `.box` (boxing is invisible to it) and `False` on
--     exactly one node, `.construct _ _ (_ :: _)`; the eraser's single `.construct`
--     construction site is nullary by explicit design. So the shape induction DOES carry
--     it, as `ShapeC`'s third conjunct (`visitExpr_shape_all`), and at the environment
--     level `NoBlockEnv` is a `RunClosed` predicate (`runClosed_noBlockEnv`).
--     `ColdStartSubject.noBlock`/`.noBlockEnv` are both deleted; the record has one field.
--
-- LEDGER: no new axiom, no `sorry`. `SEnv.walked`/`NoBlockEnv` are plain definitions over
-- `GlobalDeclarations`; `envδ` is built with lean4lean's own `VEnv.addConst`/`addDefEq` and
-- its WF with `VDecl.WF.def`, so the δ guard's environment carries exactly what `envFO`'s
-- two-axiom environment carries. The capstones' axiom sets must be UNCHANGED.
-- ============================================================================

-- The walk restriction and the conversions it enables.
#print axioms LeanToLambdaBox.SEnv.walked
#print axioms LeanToLambdaBox.SEnv.walked_lookup
#print axioms LeanToLambdaBox.SEnv.walked_bot
#print axioms LeanToLambdaBox.NoBlockEnv
#print axioms LeanToLambdaBox.registeredClosure_of_deltaMem_walked
#print axioms LeanToLambdaBox.registeredClosureData_of_deltaMem_walked
#print axioms LeanToLambdaBox.SEnvConsistent.walked

-- The rewired capstones (axiom sets unchanged), and the invariant construction that no
-- longer pins the fragment.
#print axioms LeanToLambdaBox.gBridgeInv_nil
#print axioms LeanToLambdaBox.ColdStartSubject
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart

-- The δ guard: a two-DECLARATION fragment, `g := c`, and a program that calls `g`.
-- `envδ` is `envFO` plus a real `def`, so `SEnvConsistent` is discharged from the
-- environment's own defining equation — the first non-vacuous instance of that premise in
-- the development. The `Erases`-mentioning members inherit the standing lean4lean boundary;
-- `envδ_wf`/`envδ_gc` should carry what `envFO_wf` carries.
#print axioms LeanToLambdaBox.envδ_wf
#print axioms LeanToLambdaBox.envδ_gc
#print axioms LeanToLambdaBox.envδ_senvConsistent
#print axioms LeanToLambdaBox.gDeltaMemδ
#print axioms LeanToLambdaBox.Esrcδ_walked_g
#print axioms LeanToLambdaBox.gErasesEnvDeltaDataδ
#print axioms LeanToLambdaBox.gSEvalδ
#print axioms LeanToLambdaBox.envδ_foC_d

-- ============================================================================
-- δ-inclusion, slice D6 (2026-08-12): the recursive exit's `List.mapM`, walked.
--
-- `run_rec_exit_decomp` reports only `s₁ = recConstState fixnames defs sd`, with `defs` an
-- unconstrained existential — the per-definition runs sit under a `List.mapM` and were
-- discarded. `run_rec_exit_siblings` walks that loop with an EXISTENTIALLY-LOADED
-- invariant (`run_list_mapM_ok` at a `P` that keeps the runs, not their consequences), and
-- hands back per sibling: the fetched declaration, the `prepare_erasure` and `visitExpr`
-- runs at the block's own reader, and `mkDef`'s closing equation. Pure `EraseM` reasoning,
-- so it must be sorryAx-free; `run_rec_exit_siblings_closed` adds the two output-shape
-- facts (`NoFix`/`LBClosed` of each OPEN body) that no state predicate could carry, since
-- those bodies never appear in a state.
--
-- WHAT THIS DOES AND DOES NOT UNBLOCK. Against `EnvErasureRec.erases_fix_of_open`'s
-- premise list, D6 supplies `hoclosed`, `hclose` and the length premises from the run, and
-- the per-sibling `visitExpr` runs that `hopen` needs. It does NOT supply:
--   * `hnd : ids.Nodup` — freshness, i.e. `BridgeHyps.fresh_run`; the loop rule here is
--     deliberately `gw`-free;
--   * `hreg` — "`Γ.recBodies` names the block THIS run built". Irreducible at a parameter
--     `Γ`: `Γ` is fixed before the run. This is the run-keyed agreement that should replace
--     `RegisteredClosureRec`, and it is a strictly weaker, strictly more checkable
--     assumption than an `Erases` witness;
--   * `hopen` itself — each per-sibling erasure is at `Γ.withFixvars fv`, under the run's
--     block-local fixvar map, which is the `Γ`-inside-the-motives generalisation (D8).
-- So `RegisteredClosureRec` is NOT demoted here; the gap behind it is documented
-- premise-by-premise in `ColdStartDelta`'s recursion section and at the record itself.
-- ============================================================================

#print axioms LeanToLambdaBox.run_rec_exit_siblings
#print axioms LeanToLambdaBox.run_rec_exit_siblings_closed
#print axioms LeanToLambdaBox.run_rec_exit_decomp

-- ============================================================================
-- COMPOSITION COHERENCE PASS (2026-08-13): the three walls, composed.
--
-- SUPERSEDED 2026-08-26 by the closing section of this file. Kept verbatim, because it is
-- the record of what the three walls measured on the day they composed. Two of its claims
-- have since moved and are corrected there, not here: the job/entry counts, and "R residue
-- — three, and only three" (there is now ONE, `ErasableStrengthen`; the other two were
-- retired and demoted by the δ-residue wave below).
--
-- The recursion wall (W0.1–W3.1), the Nat-literals wall (L1–L4) and the DAG cold-start
-- wall with δ-inclusion (S1–S4, D1–D6) landed as ~20 independent slices. This section
-- records what the COMPOSITION measures, so the three are audited as one artifact rather
-- than three.
--
-- MEASURED AT `cef1eb8` + this pass, from clean: `lake build` = 162 jobs, green; this
-- file = 510 `#print axioms` entries, of which 17 report NO axiom at all (the tight
-- pure-`LBTerm` layers) and 493 report a set.
--
-- THE FOUR CROWN THEOREMS PRINT ONE SET, VERBATIM AND IDENTICAL:
--
--   shipping_erase_correct_firstorder
--   shipping_erase_correct_firstorderι
--   shipping_erase_correct_firstorder_coldstart
--   shipping_erase_correct_firstorderι_coldstart
--
--     [propext, sorryAx, Classical.choice, Quot.sound,
--      Lean.Expr.instantiate1_eq, Lean.PersistentArray.toList'_push,
--      Lean.PersistentHashMap.WF.find?_eq, Lean.PersistentHashMap.WF.toList'_insert]
--
-- Three standard Lean axioms, `sorryAx` (inherited through lean4lean's `TrExprS`
-- structural lemmas, whose `proj` case calls the sorried `TrProj`), and four lean4lean
-- `Lean.Expr`/`PersistentHashMap` MODELLING axioms.
--     [CORRECTED 2026-08-27 at the `fee3ada` re-pin. The SET above is still exactly what
--      the four crown theorems print — verbatim, unmoved. The PARENTHETICAL is now false:
--      the `TrExprS` structural lemmas (`weakFV'`, `weakBV`, `mono`, `instN`) are all
--      sorryAx-FREE at `fee3ada`, and `TrProj` is no longer sorried. The `sorryAx` these
--      four still carry comes from UNIQUE TYPING — `TrExprS.uniq` → `TrProj.uniq`
--      (`PROJ-TODO`), and `IsDefEq.uniqU`, itself sorried through `IsDefEqU.weakN_iff`
--      (= C1, not discharged) and the ι fork's `pat` cases. See the re-pin section in this
--      file's header docstring for the measurement.]
-- NO AXIOM OF OURS ANYWHERE, and — the
-- point of measuring it at the composition rather than per slice — the cold-start pair
-- prints exactly what the warm pair prints. Moving the subject from an abstract
-- `visitExpr` run under a registered state to `Erasure.erase` from the EMPTY state, and
-- widening the fragment from δ-free to δ-included, cost nothing in axioms. Everything
-- those two slices added is a `Prop` premise or a derivation.
--
-- THE TRUST LEDGER lives in code, at `ColdStart.lean`'s module docstring ("THE TRUST
-- LEDGER — every premise of the two cold-start capstones, classified"), beside the D3ι
-- ledger in `FirstOrderShippingIota.lean`. It classifies EVERY premise of the two
-- cold-start capstones into four classes and nothing falls outside them:
--
--   C  proved-guard-backed certificate — `rfl`/`decide`-checkable data at a concrete
--      `Γ`/`env`, constructed in the guards: `henv`, `hnat`, `hiacoh`, `hcc`,
--      `RegBridgeHyps.knames`, `hfo` (modulo `harity`), and `hcon` at the δ guard.
--   H  runtime Hoare bundle — a spec for one REAL call on an opaque `ST`/`EIO`
--      primitive: `BridgeHyps`, `DataBridgeHyps`, `CasesBridgeHyps`, the bookkeeping
--      half of `DeltaHyps`, `RegBridgeHyps`' cold-`register_inductive` fields,
--      `PrepareHyps` (three fields — `prepare_sound` is now the THEOREM
--      `prepare_sound_of_prepareHyps`), and `IotaConsistent`. Not an axiom; not in-logic
--      decidable. The documented boundary.
--   S  scope restriction — `Us = []`, `cfg.csimp = false`, `Γ.fixvars = ⊥`,
--      `Γ.recBodies = ⊥`, `IotaRelevant`, the fragment clauses of `DeltaHyps`,
--      `ColdStartSubject.supported`, `hev`, `hfo`. A violation makes the PREMISE
--      unsatisfiable, never the theorem false.
--   R  residue — three, and only three: `RegisteredClosureRec` (the recursive δ witness;
--      what `Γ.recBodies = ⊥` stands in for, gap narrowed by D6 to `hnd`/`hreg`/`hopen`
--      at the block-local `Γ`, i.e. §W3.2/D8), `DeltaHyps.uniform` (the `∀ Δ`
--      context-uniformity, a lean4lean-side `TrExprS`-weakening obligation), and
--      `ColdStartSubject.noBlock`/`noBlockEnv` (applied form of the output and of every
--      recorded body — provably not carryable by the shape induction or by a bridge
--      motive; see slice D5's four-premise resolution above).
--
-- The run itself (`hrun`) sits outside all four: no successful run of the erasure family
-- is constructible in-logic, which is why every guard in this development leaves it
-- hypothetical.
--
-- ONE DEAD HYPOTHESIS REMOVED IN THIS PASS. `DeltaHyps.decl_run`'s fourth conjunct
-- `(Esrc n).isSome` was superseded at slice D4a by `prep_esrc` (which identifies THIS
-- run's prepared body rather than naming some body) and was projected by no consumer —
-- the single use site takes only `name_occurs n v = false`. Dropping it WEAKENS the
-- bundle, so no consumer moves and no axiom set moves.
-- ============================================================================

-- The composition, re-measured in one place: the four crown theorems must print the one
-- set quoted above, and the two derivations the ledger calls out must be theorems — both
-- are `[propext, Classical.choice, Quot.sound]`, i.e. sorryAx-FREE, which is the sharper
-- statement: what used to be a trust field is now proved without even inheriting the
-- lean4lean boundary.
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart
#print axioms LeanToLambdaBox.prepare_sound_of_prepareHyps
#print axioms LeanToLambdaBox.visitExpr_regInvShape

-- ============================================================================
-- WAVE δ-{D7a, N, rec, D7b(i)} — the three residues, revisited
--
-- 1. RESIDUE 3 (`ColdStartSubject.noBlock`/`.noBlockEnv`) — RETIRED, not discharged:
--    it was never a residue. See the corrected note above. `ShapeC` gains a third
--    output conjunct; `RunClosed.nrc`/`.rc` gain the matching slot; the two run-exit
--    lemmas are abstract in `Nf`/`Cl` and needed no change at all.
--
-- 2. RESIDUE 2 (`DeltaHyps.uniform`) — the weakening half is now a theorem with NO
--    residue (`erases_weakFV`, `erases_weak_any`). The ledger blamed the wrong side:
--    `TrExprS.weakFV` has been proved upstream all along; what is missing is
--    `Erasable`/`HasType` STRENGTHENING, which is the commissioned obligation.
--    Correction to the design: lean4lean's `weakFV` wants `VLCtx.WF` of the target
--    context, and the `lam`/`letE` cases cannot re-establish it (`Erases.lam` carries no
--    `IsType` for its binder type). `VLCtx.FVWF` is all the proof consumes and conses
--    freely under a bvar entry — hence the `_fvwf` transcriptions. For the unrestricted
--    `∀ Δf` that `Erases.fix` demands, even `FVWF` is unavailable; there the
--    fvar-FREENESS of the source removes the hypothesis outright (no `.inr` lookup ever
--    happens), hence the `_nofvars` transcriptions and `erases_weak_any`.
--
-- 3. `erases_fix_of_open` — its `hopen` premise was UNSATISFIABLE for every
--    self-referential block, and unguarded. `Erases.fixvar` is the only rule with source
--    `.const` and target `.fvar`, and its `hfresh` is anti-monotone in `Δ`. Repaired by
--    conditioning `hopen` on a fresh `Δf` and rebuilding `Erases.fix`'s unrestricted
--    `hbodies` through `[]` with `erases_weak_any`. `gErases_fix_of_open` is the guard
--    it never had.
--
-- AXIOM MOVEMENT: none at the capstones. The new NoBlock lemmas are sorryAx-FREE (they
-- touch no lean4lean witness). The `Erases`-transport lemmas inherit `sorryAx` through
-- lean4lean's `TrProj.weak'`, which is the boundary the capstones already measure, and
-- the fragment excludes `.proj` anyway.
--     [CORRECTED 2026-08-27 at `fee3ada`. `TrProj.weak'` came back PROVED (A3), so it is
--      no longer a boundary at all, and the `Erases`-transport lemmas below —
--      `TrExprS.weakFV_fvwf`, `erases_weakFV`, `TrExprS.weakFV_nofvars`,
--      `erases_weak_any`, `erases_fix_of_open`, `gErases_fix_of_open`,
--      `BridgeInv.vlctx_wf`, `BridgeInv.noBV` — are all sorryAx-FREE now. The only
--      downstream cost of A0 was passing `henv` at the two `proj` arms in
--      `ErasesStrengthen.lean`, since `TrProj.weak'` gained an `Ordered env` premise.]
-- ============================================================================

-- Residue 3, retired.
#print axioms LeanToLambdaBox.noBlock_toBvar
#print axioms LeanToLambdaBox.noBlock_foldl_zipIdx_map
#print axioms LeanToLambdaBox.rec_block_noBlock
#print axioms LeanToLambdaBox.visitExpr_shape_all
#print axioms LeanToLambdaBox.visitExpr_noBlock
#print axioms LeanToLambdaBox.runClosed_noBlockEnv
#print axioms LeanToLambdaBox.visitExpr_noBlockEnv

-- Residue 2, weakening half.
#print axioms LeanToLambdaBox.VLCtx.FVWF.fvars_nodup
#print axioms LeanToLambdaBox.TrExprS.weakFV_fvwf
#print axioms LeanToLambdaBox.erases_weakFV
#print axioms LeanToLambdaBox.TrExprS.weakFV_nofvars
#print axioms LeanToLambdaBox.erases_weak_any

-- The repaired recursion theorem and its new guard.
#print axioms LeanToLambdaBox.erases_fix_of_open
#print axioms LeanToLambdaBox.gErases_fix_of_open

-- The δ record's context data.
#print axioms LeanToLambdaBox.BridgeInv.vlctx_wf
#print axioms LeanToLambdaBox.BridgeInv.noBV

-- Stability: the two cold-start capstones, unchanged.
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart

-- ============================================================================
-- WAVE δ-D7b — context-uniformity, discharged
--
-- `DeltaHyps.uniform` is GONE. The two-sided transport it asserted is now
-- `ErasesUniform.erases_uniform_closed` = strengthen-to-`[]` then `erases_weak_any`.
--
-- What survives is exactly ONE named obligation, `ErasableStrengthen`: `HasType.weakN_inv`
-- for the shipping `VEnv.HasType`. Two upstream facts established while proving this, both
-- worth recording because they contradict the design pass:
--   * lean4lean does NOT prove `HasType.weakN_inv` for the stratified theories — those
--     statements sit inside comment blocks whose supporting `IsDefEq.weakN_inv` has `sorry`
--     arms;
--   * for the shipping `VEnv.HasType` the corresponding `IsDefEqU.weakN_iff`
--     (`Theory/Typing/UniqueTyping.lean`) is itself a `sorry`.
-- So discharging it from what upstream has today would import a gap, not close one.
--
-- The `box` arm DID close, and without a second obligation, via lean4lean's
-- `TrExprS.unique` — which is `sorry`-free but gated on `TrExprS.IsUnique e`
-- (projection-free). `NoProj` is that gate, and `DeltaHyps.esrc_shape` is where the
-- fragment pays it; the supported fragment excludes `.proj` anyway.
--
-- AXIOM MOVEMENT: none at the capstones. Everything mentioning `Erases` carries `sorryAx`
-- already — `TrProj` is a `sorry`-valued DEFINITION upstream and `Erases.box`/`lam`/`letE`
-- mention `TrExprS`, so `#print axioms LeanToLambdaBox.Erases` has carried it from the
-- start.
--     [CORRECTED 2026-08-27 at `fee3ada`, and this is the annotation the re-pin most
--      directly overturns. That mechanism is DEAD: A1 replaced the `sorry`-valued `def`
--      with a real one, `#print axioms Lean4Lean.TrProj` is `[propext]`, and mentioning
--      `Erases`/`TrExprS` now costs nothing. It is what retired 111 declarations in this
--      file at a stroke — including `visitExpr_refines_erases` itself. Of the entries
--      listed just below, `Erases.strengthen_fvlift` and `erases_uniform_of_nil` went
--      clean; `erases_strengthen_closed` and `erases_uniform_closed` did NOT, because they
--      genuinely consume `.uniq`. `ErasableStrengthen` was `[propext]` before and after —
--      it is a Prop, never an axiom, and C1 not landing does not change that.]
-- ============================================================================

#print axioms LeanToLambdaBox.ErasableStrengthen
#print axioms LeanToLambdaBox.erasableStrengthen_liftN_zero
#print axioms LeanToLambdaBox.NoProj.toIsUnique
#print axioms LeanToLambdaBox.Erases.strengthen_fvlift
#print axioms LeanToLambdaBox.erases_strengthen_closed
#print axioms LeanToLambdaBox.erases_uniform_closed
#print axioms LeanToLambdaBox.erases_uniform_of_nil

-- Stability, once more, with the residue discharged.
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart

-- ============================================================================
-- WAVE δ-D8 — the bridge goes inside the block, and `RegisteredClosureRec` is demoted
--
-- THE EXPERIMENT AND ITS RESULT. `visitExpr_refines_erases` binds `Γ` as a plain implicit
-- and `VisitExprRefines.lean` contains no `variable` command at all, so the theorem is
-- Γ-polymorphic AS A STATEMENT and every application picks its own `Γ`. Instantiating it
-- at the block-local `Γ' := Γ.withFixvars fv` — the reader `visitMutual` installs while
-- erasing a mutual block — therefore needs NO motive change. Of its premises, EXACTLY ONE
-- breaks, as the design predicted:
--
--   BridgeHyps / DataBridgeHyps / CasesBridgeHyps  read only `Γ.ctors`, `Γ.casesOns`,
--     `Γ.ctorArities`, `Γ.casesDiscrPos`, `Γ.ctorFields` — every one `rfl` at
--     `withFixvars`. The three transports are field-by-field, zero obligations.
--   BridgeInv  rebuilt by `BridgeInv.withFixvars`: six fields are literally `Γ`'s or never
--     mentioned `Γ`; the two fixvar fields become the reader-vs-`fv` agreement (which the
--     `withReader` establishes by construction) and the block freshness (`fresh_run`
--     against `BridgeInv.reserved`). `known` is unconstrained — the invariant has not
--     mentioned it since D4a retired `known_dom`, which is precisely what lets the block's
--     inner runs be taken at `known = ⊥`.
--   Supported  transports and GROWS: `Supported.const`'s `known n ∨ Γ.fixvars n ≠ none`
--     gains the whole block as its second disjunct.
--   TrExprS witness, env.Ordered  never mentioned `Γ`.
--   DeltaHyps  THE ONE BREAK. `nofixvars` asserted `Γ.fixvars = ⊥` unconditionally, which
--     is FALSE at a block-local `Γ` (`gNofixvars_blocklocal_refuted`). It is now
--     conditioned on the fragment, `∀ {n}, known n → …`, which is all its two consumption
--     sites (both under `hkn : known n`) ever had in scope. `of_bot` loses its `hnfv`
--     argument — the tell that the field did nothing at `known = ⊥`.
--
-- WHAT THAT BUYS. `RegisteredClosureRec` stops being a certificate:
-- `erases_rec_block_of_run` derives its `erase` field from D6's per-sibling runs plus the
-- instantiated bridge plus `erases_fix_of_open_nil`, and `recEnvConsistent_of_block`
-- derives `RecEnvConsistent` outright. What survives is a REGISTRATION AGREEMENT —
-- `hreg`/`hfv`/`hcov`, "the `Γ` you supply names this block, under the map the run
-- installed" — irreducible at a parameter `Γ` and of `BridgeInv.knames` class, plus the
-- standing `hnest` residue. Scope cost, named: a block's bodies call only its own
-- siblings, registered constructors and registered `casesOn`s.
--
-- ALSO: `erases_fix_of_open_nil`. Slice `rec` conditioned `hopen` on a fresh `Δf`, but the
-- proof instantiates it at `Δf := []` and NOWHERE else, so the `∀ Δf` is not load-bearing.
-- The `[]`-only form is the one a run can supply; `erases_fix_of_open` is now its
-- corollary, signature verbatim.
--
-- THE CLAIM THAT FAILED, and it is not in the Γ-instantiation. The design expected the
-- capstones' `hnorec : Γ.recBodies = ⊥` to trade for the run-keyed agreement. It cannot,
-- yet, and the obstruction is upstream of everything above: `DeltaHyps.decl_run` demands
-- `name_occurs n v = false` of every fragment name, which forces `visitMutual`'s
-- `nonrecursive` test `true`, so the bridge's step 6 REFUTES the recursive exit instead of
-- walking it. A cold start never takes that exit inside the fragment, so there is no run
-- for these theorems to consume there. Wiring them in means giving step 6 a recursive
-- branch — `RunConclδ`'s `δ` transport across `recConstState` (which IS
-- `erases_rec_block_of_run`'s conclusion, so it composes), the block loop's generator
-- bookkeeping, and one more scope restriction, since the registration is keyed on
-- `remove_unsafe_rec n` and not on `n`.
--     [δ-D8e: this diagnosis is CORRECT ABOUT THE GATE and INCOMPLETE ABOUT THE REST.
--      The wiring list above omits a structural item that no premise supplies. See the
--      δ-D8e section at the end of this file.]
--
-- AXIOM MOVEMENT: none at the capstones, verbatim. The transports are pure record
-- surgery, and two of them (`DataBridgeHyps`, `CasesBridgeHyps`) come out sorryAx-FREE
-- along with `supported_const_fixOpen_not_ambient` and the two `nofixvars` guards; the
-- other two mention `TrExprS`, and the composition mentions `Erases`, so both inherit the
-- same lean4lean `TrProj` boundary those types have carried from the start.
--     [CORRECTED 2026-08-27 at `fee3ada`: the other two now come out sorryAx-FREE as well.
--      `BridgeHyps.withFixvars`, `BridgeInv.withFixvars` and `visitExpr_refines_erases_block`
--      all measure clean, because "mentions `TrExprS`/`Erases`" stopped implying anything
--      once `TrProj` got a definition. The entire δ-D8 slice is now sorryAx-free.]
-- ============================================================================

-- The instantiation: the bundle transports, the invariant, and the packaged bridge.
#print axioms LeanToLambdaBox.BridgeHyps.withFixvars
#print axioms LeanToLambdaBox.DataBridgeHyps.withFixvars
#print axioms LeanToLambdaBox.CasesBridgeHyps.withFixvars
#print axioms LeanToLambdaBox.BridgeInv.withFixvars
#print axioms LeanToLambdaBox.visitExpr_refines_erases_block
#print axioms LeanToLambdaBox.supported_const_fixOpen_not_ambient

-- The one break, and the two guards that make it load-bearing.
#print axioms LeanToLambdaBox.DeltaHyps.of_bot
#print axioms LeanToLambdaBox.gNofixvars_blocklocal_refuted
#print axioms LeanToLambdaBox.gNofixvars_blocklocal
#print axioms LeanToLambdaBox.gDeltaScope

-- The `[]`-only recursion theorem.
#print axioms LeanToLambdaBox.erases_fix_of_open_nil
#print axioms LeanToLambdaBox.erases_fix_of_open

-- The glue to the run: `mkDef`'s reader-lookup fold IS `closeFix ids 0`, once the block
-- names are distinct — the "modulo the `fixvars` lookup" `FixMetatheory` had always left
-- open. All four are sorryAx-FREE: pure list/HashMap reasoning.
#print axioms LeanToLambdaBox.zip_pairwise_fst
#print axioms LeanToLambdaBox.blockMap_getElem!
#print axioms LeanToLambdaBox.blockMap_getElem?_inv
#print axioms LeanToLambdaBox.closeFix_eq_block_fold
#print axioms LeanToLambdaBox.run_rec_exit_siblings_close

-- The demotion, and its guard on the self-referential fixture.
#print axioms LeanToLambdaBox.erases_rec_block_of_run
#print axioms LeanToLambdaBox.recEnvConsistent_of_block
#print axioms LeanToLambdaBox.gErasesRecBlockD8
#print axioms LeanToLambdaBox.gRecEnvConsistentD8

-- Stability: the two cold-start capstones, verbatim unchanged.
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart

-- ============================================================================
-- SLICE δ-D8e — the recursion trade, priced; and one premise that stops being one
--
-- The slice set out to walk the recursive exit and retire `hnorec` from both cold-start
-- capstones. It lands two of the four steps and PRICES the other two, because the price
-- turned out to be a motive change rather than a premise.
--
-- (1) THE `decl_run` RELAXATION — landed. The clause `name_occurs n v = false` was the
--     fifth conjunct of a spec about `Compiler.LCNF.getDeclInfo?`, and it is not about
--     the fetch at all. It is now `DeltaHyps.nonrecursive`, its own field, keyed on the
--     two runs its consumer holds (the fetch, which ties the value to the name, and the
--     `value?` hit) in `prep_esrc`'s style. `decl_run` is left with what the fetch
--     answers; `nonrecursive` is scope restriction 5, listed with the other four. The
--     trade is now a one-field trade. `of_bot` absorbs the new field for free — it is
--     keyed on `known n`.
--
-- (2) `hffv` — landed, and NOT where D8 filed it. D8 asked for a fourth `ShapeC`
--     conjunct, `FVarsIn (fun _ => False)` on `visitExpr`'s outputs. That is FALSE:
--     inside a block `visitConst` returns `.fvar x` for a sibling, and the repo's own
--     fixture has `gObodyD8 x = λa. x #0`. Fvar-freeness is a property of the STORED
--     body, after `mkDef` closes — and it is not an independent property even there. It
--     is a consequence of the block-local erasure plus the closing:
--       `erases_target_fvars`   an fvar-free SOURCE erases to a target whose free
--                               variables are all fixvars of `Γ` (the `Erases.fvar` rule
--                               is the only one that could invent one, and the source-side
--                               hypothesis kills it; `const_fix`/`fix` are killed by their
--                               own `htobv`),
--       `not_hasFVar_closeFix`  a term whose fvars lie in `ids` closes to one with none,
--                               on top of `hasFVar_toBvar` — `toBvar y` deletes exactly
--                               `y` and manufactures nothing.
--     So `erases_rec_block_of_run` DROPS `hffv` from its signature and derives it. Net:
--     one fewer premise on the δ-D8b theorem, and the shape induction is untouched.
--
-- (3) STEP 6's RECURSIVE BRANCH — NOT landed, and the reason is structural, which is the
--     correction to δ-D8's ledger entry. Removing `nonrecursive` lets the run REACH the
--     recursive exit; it does not let the bridge WALK it.
--
--     Inside `visitExpr_refines_erases_core` the exit's per-sibling erasures are runs of
--     the induction's ABSTRACT fixpoint argument, so the only thing available about them
--     is the motives — and the motives fix one `Γ`. The exit erases each sibling under
--     the reader carrying the block's fixvar map, while `BridgeInv.fixvars` is an IFF
--     against `Γ.fixvars`, which `DeltaHyps.nofixvars` pins at `⊥` for a fragment name —
--     and step 6 has `hkn : known n` in scope. So the erasure IH's own premise is FALSE
--     at the configuration the branch would have to run it in:
--       `bridgeInv_blockReader_refuted`        (any reader map with a hit),
--       `bridgeInv_rec_exit_reader_refuted`    (the block reader itself, one sibling).
--     δ-D8a's finding stands and is about the THEOREM: `visitExpr_refines_erases` is
--     Γ-polymorphic as a statement, which is what `visitExpr_refines_erases_block` reads
--     it at a second `Γ` from. Step 6 has no outside to read it from.
--
--     PRICED, in order: quantify `(known, Γ, Esrc)` and the four trust bundles inside all
--     eighteen motives (~40 IH sites, ~30 bundle uses); a block-loop decomposition that
--     CHAINS states and worlds, since `run_rec_exit_siblings` is `gw`-free by design and
--     hands its per-sibling runs back at unrelated states — exactly what a `BridgeInv`
--     cannot be rebuilt from; the transport of the OUTER δ record across the block's
--     inner runs; the block-local `Supported`/`TrExprS`/`Esrc` premises for the sibling
--     bodies, which the `known = ⊥` bundle cannot supply because every scope field of it
--     is keyed on `known n`; and the `remove_unsafe_rec` restriction, which is real:
--       `rec_exit_registers_stripped_name` — the exit registers under
--       `names.map remove_unsafe_rec`, so at `f._unsafe_rec` motive 6's
--       `(s'.constants.get? n).isSome` is FALSE on the run, not merely unproved.
--
-- (4) THE CAPSTONE TRADE — NOT landed, and deliberately. Taking `hcov` (a membership
--     agreement) in place of `hnorec` would LOOK like a widening and would not be one: the
--     only exit that cons a `.constantDecl ⟨some (.fix …)⟩` is the recursive one, and the
--     non-recursive exit provably cannot (`nonrec_exit_stores_no_fix`: it stores a
--     `visitExpr` output, and those are `NoFix`). With no producer, the membership premise
--     is uninhabited for every `n` with `Γ.recBodies n ≠ none`, so the traded capstone
--     would speak about exactly the same programs while hiding the restriction inside a
--     premise instead of naming it in the ledger. It waits for (3).
--
-- AXIOM MOVEMENT: none at the capstones, verbatim, again — same eight, third slice
-- running. The three pure-`LBTerm` fvar lemmas are sorryAx-FREE (`propext`, `Quot.sound`),
-- and so are `rec_exit_registers_stripped_name` and `nonrec_exit_stores_no_fix`. The two
-- `BridgeInv` refutations are NOT, and not for their own sakes: `BridgeInv.mlc` carries an
-- `MLCtx.WF`, hence `TrExprS`, hence the lean4lean `TrProj` boundary — the same one
-- `erases_target_fvars` inherits through `Erases`. Nothing new is trusted either way; a
-- refutation that inherits a boundary is still a refutation.
--     [CORRECTED 2026-08-27 at `fee3ada`: there is no longer a boundary to inherit. Both
--      `BridgeInv` refutations and `erases_target_fvars` are sorryAx-FREE now — the
--      `TrProj`-through-`TrExprS` channel they described was the definitional taint, and
--      A1 closed it. The refutations are unconditional.]
-- ============================================================================

-- (1) The split: `decl_run` without the recursion clause, `nonrecursive` beside it.
#print axioms LeanToLambdaBox.DeltaHyps.of_bot

-- (2) The fvar kit. sorryAx-FREE: pure `LBTerm` reasoning.
#print axioms LeanToLambdaBox.hasFVar_toBvar
#print axioms LeanToLambdaBox.not_hasFVar_closeFixFold
#print axioms LeanToLambdaBox.not_hasFVar_closeFix
-- …and the one `Erases`-level fact that counts fvars.
#print axioms LeanToLambdaBox.erases_target_fvars
-- …cashed in: `hffv` is gone from this signature.
#check @LeanToLambdaBox.erases_rec_block_of_run
#print axioms LeanToLambdaBox.erases_rec_block_of_run
#print axioms LeanToLambdaBox.gErasesRecBlockD8

-- (3) The wall, as theorems. [2026-08-27, `fee3ada`: all three are sorryAx-FREE. The two
-- `BridgeInv` ones used to inherit the definitional `TrProj` taint through
-- `BridgeInv.mlc`; that channel is gone.]
#print axioms LeanToLambdaBox.bridgeInv_blockReader_refuted
#print axioms LeanToLambdaBox.bridgeInv_rec_exit_reader_refuted
#print axioms LeanToLambdaBox.rec_exit_registers_stripped_name

-- (4) Why the capstone half cannot go first.
#print axioms LeanToLambdaBox.nonrec_exit_stores_no_fix

-- Stability: the two cold-start capstones, verbatim unchanged, for the third slice running.
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart

-- ============================================================================
-- COMPOSITION COHERENCE PASS (2026-08-26): the δ-residue week, composed.
--
-- SUPERSEDES the 2026-08-13 composition section above, which is kept as the record of
-- what the three walls measured on the day they composed. Everything since — the
-- verify_bench duplicates, δ-D7a, δ-N, `rec`, δ-D7b(i)/D7b, δ-D8a–d and δ-D8e/a–c —
-- landed as thirteen slices whose common subject is the RESIDUE LIST, and this section
-- records what the composition of those thirteen measures.
--
-- MEASURED AT `506d9c8` + this pass, from clean:
--   `lake build`             = 163 jobs, green.
--   `lake build VerifyBench` = 168 jobs, green (the five csimp-off duplicates; a separate
--                              `lean_lib`, deliberately outside `defaultTargets`).
--   this file                = 584 `#print axioms` entries, of which 19 report NO axiom
--                              at all (the tight pure-`LBTerm` layers) and 565 report a
--                              set.
--
-- THE FOUR CROWN THEOREMS PRINT ONE SET, VERBATIM AND IDENTICAL — the same eight as at
-- `cef1eb8`, unmoved through thirteen slices:
--
--   shipping_erase_correct_firstorder
--   shipping_erase_correct_firstorderι
--   shipping_erase_correct_firstorder_coldstart
--   shipping_erase_correct_firstorderι_coldstart
--
--     [propext, sorryAx, Classical.choice, Quot.sound,
--      Lean.Expr.instantiate1_eq, Lean.PersistentArray.toList'_push,
--      Lean.PersistentHashMap.WF.find?_eq, Lean.PersistentHashMap.WF.toList'_insert]
--
-- Discharging a residue, retiring a premise and demoting a record cost NOTHING in axioms,
-- in either direction. No axiom of ours anywhere; no `sorry` of ours anywhere.
--
-- WHAT MOVED IN THE LEDGER, and it is the whole point of the week: class R went from
-- THREE to ONE.
--
--   R (was) `RegisteredClosureRec`      -> DEMOTED (δ-D8). Never a capstone premise;
--                                          `hnorec` (class S) always stood in for it. Its
--                                          `erase` field is derived
--                                          (`erases_rec_block_of_run`); a registration
--                                          agreement survives.
--   R (was) `DeltaHyps.uniform`         -> DISCHARGED (δ-D7b). The field is DELETED. What
--                                          replaces it is ONE commissioned `VExpr`-level
--                                          obligation, `ErasableStrengthen`, carried as an
--                                          explicit capstone premise `hstr`.
--   R (was) `ColdStartSubject.noBlock`  -> RETIRED (δ-N). It was never a residue: `NoBlock`
--           `.noBlockEnv`                 is `ShapeC`'s third conjunct and `NoBlockEnv` is
--                                          a `RunClosed` predicate. `ColdStartSubject` is
--                                          down to ONE field.
--   R (now) `ErasableStrengthen`        -> the only one. Commissioned upstream, not
--                                          assumed: `../lean4lean/trproj-commission.md`
--                                          Cluster 2. Its PROOF disjunct is ~5 lines once
--                                          `IsDefEqU.weakN_iff`'s forward direction lands;
--                                          the `IsArityUpTo` disjunct (forallE inversion
--                                          through a lift) is the real frontier.
--
-- TWO REFUTATIONS PRICE THE ONE THING THE WEEK DID NOT LAND. `hnorec` is still class S,
-- and δ-D8e established WHY in machine-checked form rather than by estimate:
-- `bridgeInv_blockReader_refuted` / `bridgeInv_rec_exit_reader_refuted` show the erasure
-- IH's own premise is FALSE at the block's reader, so the Γ-inside-the-motives
-- generalisation is necessary INSIDE the induction even though δ-D8 correctly found it
-- unnecessary for the bridge theorem as a STATEMENT. `nonrec_exit_stores_no_fix` shows the
-- capstone half cannot be landed ahead of that producer without replacing a named scope
-- restriction by an uninhabited premise. Both are in the ledger, priced.
--
-- ONE SHIPPING FINDING RAISED, NOT PATCHED, and it came from running the eraser rather
-- than from proving about it: `VerifyBench/STATUS.md`'s sparse-`casesOn` panic
-- (`notes/EQUIV_FINDINGS.md` D12). It is findings D4/D5 firing on real benchmark code —
-- `visitCases` reads the inductive off `casesInfo.declName.getPrefix` instead of
-- `casesInfo.indName`, the `unreachable!` returns `default : LBTerm = .box` (finding D7),
-- and `Quicksort` erases to a program that returns box on every non-empty list, exit 0,
-- well-formed `.ast`. Shipping code, left byte-unchanged.
-- ============================================================================

-- The composition, re-measured in one place, for the last time this week.
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart

-- The three ledger movements, as declarations rather than as prose.
-- `uniform`, discharged: the two halves and the composition.
#print axioms LeanToLambdaBox.erases_weak_any
#print axioms LeanToLambdaBox.erases_strengthen_closed
#print axioms LeanToLambdaBox.erases_uniform_closed
-- `noBlock`, retired: the output-shape conjunct and its environment form.
#print axioms LeanToLambdaBox.visitExpr_noBlock
#print axioms LeanToLambdaBox.visitExpr_noBlockEnv
-- `RegisteredClosureRec`, demoted: the derived `erase` field and `RecEnvConsistent`.
#print axioms LeanToLambdaBox.erases_rec_block_of_run
#print axioms LeanToLambdaBox.recEnvConsistent_of_block

-- ============================================================================
-- RE-PIN 2026-08-27: lean4lean `1a1ebe8` (iota) -> `fee3ada` (trproj)
--
-- SUPERSEDES the 2026-08-26 composition section above ONLY on axiom provenance. Its
-- ledger movements (R three -> one) stand unchanged; its crown-four SET stands unchanged;
-- its explanation of WHY that set contains `sorryAx` does not. Every annotation in this
-- file that blamed `TrProj` now carries a bracketed correction in place, and the header
-- docstring carries the full measurement.
--
-- MEASURED AT this commit, from clean:
--   `lake build`             = 167 jobs, green (was 163; the four new jobs are lean4lean's,
--                              from master's `Verify/Level`, `NormLt`, `QSort`,
--                              `Theory/LevelSat`, which the merge brings along).
--   `lake build VerifyBench` = 172 jobs, green (was 168).
--   this file                = 596 `#print axioms` entries (584 + the 12 below), of which
--                              19 report NO axiom at all and 577 report a set.
--
-- WHAT THE RE-PIN COST IN CODE: two tokens. `TrProj.weak'` gained an `Ordered env`
-- premise (A3), so the two downstream re-proofs of lean4lean's `TrExprS.weakFV'` on weaker
-- premises pass `henv` at their `proj` arms (`ErasesStrengthen.lean`, both already had it
-- in scope). One further straggler the migration survey did not predict: master's new
-- `VExpr` kit for the `TrProj` proofs introduced `Lean4Lean.VExpr.mkApps_concat`, which
-- collided by name with the identical snoc lemma `IotaPattern.lean` had been carrying;
-- the local copy is deleted and the use site resolves upstream.
--
-- WHAT IT COST IN AXIOMS: two, and neither from the commissioned work.
-- `trproj` is a MERGE OF MASTER, and master added `Std.TreeMap.all_eq_all_toList` to
-- `Verify/Axioms.lean` and made `Lean.Level.isExplicitSubsumedAux_eq` reachable. They land
-- on the executable kernel-checker cluster and nowhere else — three entries:
-- `TypeChecker.kernel_isErasable_sound`, `ResidualHyps.toBridgeHyps`,
-- `shipping_visitExpr_correct'`. The commissioned two commits add no `axiom` at all.
--
-- WHAT IT BOUGHT: 139 entries (111 distinct declarations) lost `sorryAx` outright.
-- Entries carrying `sorryAx`: 230 -> 91. The mechanism is one line —
-- `#print axioms Lean4Lean.TrProj` is now `[propext]`, where it used to be a
-- `sorry`-valued DEFINITION, and a `sorry` in a definition taints the TYPE of every
-- statement mentioning `TrExprS`, proof or no proof.
--
-- THE LINE WORTH QUOTING: **`visitExpr_refines_erases` is sorryAx-free.** The claim that
-- the shipping eraser refines the `Erases` relation no longer rests on any lean4lean gap;
-- it rests only on the `Expr`/`PersistentHashMap` modelling axioms. Same for its `_core`
-- and `_block` forms, for `BridgeInv` and every transport of it, for `DeltaHyps`/
-- `DeltaMem`/`RunConclδ`/`ColdStartSubject`, for the whole δ registration chain, and for
-- every `Erases` transport and inversion lemma.
--
-- WHAT DID NOT MOVE, AND WHY THE CAPSTONES DID NOT: the forward-simulation half consumes
-- UNIQUE TYPING, which the trproj round did not close and was not asked to. `TrExprS.uniq`
-- (69 downstream call sites, 31 in `ErasesCorrectData.lean`) bottoms out in `TrProj.uniq`,
-- still `PROJ-TODO`; `IsDefEq.uniqU` bottoms out in `IsDefEqU.weakN_iff`, which is
-- commission item C1 — NOT discharged, and the delivered analysis argues it cannot be
-- discharged from what upstream has today (module import cycle: `ChurchRosser.lean`
-- imports `UniqueTyping.lean`; plus a same-measure logical cycle). `ErasableStrengthen`
-- therefore stays a named premise, exactly as the 2026-08-26 ledger has it.
--
-- THE TWO PROJ-TODOs THAT DO NOT REACH US: `TrProj.weak'_inv` (nothing here calls
-- `TrExprS.weakFV'_inv` — the `ErasesUniform` design routed around it, and that decision
-- pays off again here) and `TrEnv.proj_defeq` (a real STATEMENT with a deferred proof; a
-- new interface, deliberately not yet consumed).
-- ============================================================================

-- (1) The mechanism, measured rather than asserted: the definition that used to be a
-- `sorry`, and the four `TrExprS` structural lemmas it used to taint.
#print axioms Lean4Lean.TrProj
#print axioms Lean4Lean.TrExprS.weakFV'
#print axioms Lean4Lean.TrExprS.mono
#print axioms Lean4Lean.TrExprS.instN

-- (2) The residue, also measured: what unique typing still costs.
#print axioms Lean4Lean.TrProj.uniq
#print axioms Lean4Lean.TrExprS.uniq
#print axioms Lean4Lean.VEnv.IsDefEqU.weakN_iff

-- (3) The headline retirement: the bridge, and the δ chain behind it.
#print axioms LeanToLambdaBox.visitExpr_refines_erases
#print axioms LeanToLambdaBox.visitExpr_refines_erases_block
#print axioms LeanToLambdaBox.Erases.abstract

-- (4) Stability: the crown four are represented by the warm pair; the set is verbatim
-- what the 2026-08-26 composition recorded.
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι

-- ============================================================================
-- SLICE Γ-W0 — foundations for the Γ-in-motives generalisation
--
-- THE MEASUREMENT THAT COMES FIRST (design risk 3, "check this empirically in W0, before
-- committing to the slice"). `Compiler.LCNF.getDeclInfo? n` is `env.find? (mkUnsafeRecName
-- n) <|> env.find? n` (`Lean/Compiler/LCNF/ToDecl.lean`) — the unsafe-recursive version is
-- tried FIRST. Measured on the §H benchmarks' arithmetic, at this toolchain:
--
--   Nat.add / Nat.mul / Nat.sub / Nat.pow / Nat.ble / Nat.beq
--   List.length / List.append / List.map / List.foldl
--       getDeclInfo? ↦ ci.name = `n._unsafe_rec`,  ci.all = [n._unsafe_rec],
--       name_occurs n ci.value! = true  ⟹  `nonrecursive` FALSE, the exit IS taken
--   Nat.div / Nat.mod / Nat.decEq / Nat.repr / List.reverse
--       no `._unsafe_rec` in the environment; ci.all = [n]; the non-recursive exit
--
-- Two consequences, in opposite directions:
--
--  (a) `BlockHyps.stripped : known n → remove_unsafe_rec n = n` is NOT the problem the
--      design feared. `n` there is `visitMutual`'s ARGUMENT — the name the source
--      mentions, `Nat.add` — and `remove_unsafe_rec Nat.add = Nat.add`. The `._unsafe_rec`
--      names appear only inside `ci.all`, and registration is under
--      `ci.all.map remove_unsafe_rec = [Nat.add]`, which is exactly what motive 6's
--      registration conclusion asks for. Measured end-to-end: `VerifyBench/ast/Arith.ast`
--      contains four `tFix` and ZERO occurrences of `_unsafe_rec`.
--
--  (b) `DeltaHyps.decl_run`'s `ci.all = [n]` conjunct is FALSE at exactly those names —
--      it is `[n._unsafe_rec]`. So the fragment `known` cannot contain `Nat.add` as the
--      bundle stands, and the benchmark payoff needs that conjunct relaxed to
--      `∃ m, ci.all = [m] ∧ remove_unsafe_rec m = n` (the `single_decl` test the run
--      actually performs is `ci.all.length == 1`, which holds). Likewise the block-local
--      scope fields the design keys on `known m` for `m ∈ ci.all` must be keyed on
--      `known (remove_unsafe_rec m)`. Recorded here as a W2 item; no code moves in W0.
--
-- WHAT LANDED. Five lemmas plus the coherence glue, all additive; the audit output below
-- was byte-identical before and after the slice for every pre-existing entry.
-- ============================================================================

-- (1) The coherence equation `hΓ : Γ = Γ₀.withFixvars Γ.fixvars` is `rfl` at both ends.
#print axioms ErasureCtx.withFixvars_self
#print axioms ErasureCtx.withFixvars_withFixvars

-- (2) The fragment enters a block, and grows there.
#print axioms LeanToLambdaBox.Supported.withFixvars

-- (3) The two block loops, chained (Lemmas A and B), and the block registration as a
-- `RunConcl` step.
#print axioms Erasure.run_mkFreshFVarId_list
#print axioms Erasure.run_rec_exit_siblings_chained
#print axioms Erasure.runConcl_recConstState

-- (4) The δ record's second extension step.
#print axioms LeanToLambdaBox.DeltaMem.recBlock
#print axioms LeanToLambdaBox.RunConclδ.recBlock

-- ============================================================================
-- SLICE Γ-W1 — the motives quantify `Γ`
--
-- THE CHANGE, MEASURED. Inside `visitExpr_refines_erases_core`, every motive with content
-- gained two binders immediately after its run hypothesis,
--
--     ∀ (Γ : ErasureCtx) (_hΓ : Γ = Γ₀.withFixvars Γ.fixvars) Δ, …
--
-- and its `RunConclδ` conjunct was re-indexed to the ambient `Γ₀`. Counted on the diff:
-- 34 motive-signature edits (17 in the theorem's own statement, 17 in the `(motive_i := …)`
-- block — motive 10's conclusion is `True` and nothing calls it, so it stays fixed and the
-- design's "36" is 34 here), 42 `RunConclδ` re-indexes, 17 `intro` lines, 33 IH argument
-- insertions, 12 bundle transports across 9 steps, and one manual site — step 6's callee
-- invariant `hinv'`, retargeted from the motive-local `Γ` to `Γ₀`.
--
-- WHAT DID **NOT** MOVE, and this is the whole design:
--   * the 18 `eraseM_admissible_ok` obligations — the binders live inside the `Q` those
--     helpers quantify, so admissibility never sees them;
--   * the ~135 `Erases env Us Γ` / `BridgeInv … Γ` / `Supported known Γ` / `Γ.…` mentions
--     inside the step bodies — `Γ` is still a variable literally named `Γ`;
--   * `known`, `Esrc`, and all four premise bundles, which stay outer at `Γ₀`;
--   * every consumer. `visitExpr_refines_erases` is the `Γ := Γ₀`,
--     `hΓ := (withFixvars_self Γ).symm` corollary and its four call sites are untouched;
--     `visitExpr_refines_erases_block` and all eight NonVacuity guards are untouched.
--
-- ELABORATION. The mitigation for the design's top risk was to keep `Γ` a bound *variable*
-- rather than substituting `Γ₀.withFixvars fv`, so the goal terms do not grow. Measured:
-- `lake env lean LeanToLambdaBox/VisitExprRefines.lean` runs at 6.05s / 7.81s user after
-- the change against 6.07s / 7.83s user before — no delta, at the unchanged
-- `maxHeartbeats 1000000`.
--
-- AXIOM MOVEMENT: **none**, anywhere. This file's entire output is byte-identical to the
-- Γ-W0 run, which was itself byte-identical to the pre-slice baseline.
-- ============================================================================

-- The three obligation-free bundle transports the steps run on, and the two registration
-- projections the coherence equation shares.
#print axioms LeanToLambdaBox.BridgeHyps.of_coh
#print axioms LeanToLambdaBox.DataBridgeHyps.of_coh
#print axioms LeanToLambdaBox.CasesBridgeHyps.of_coh
#print axioms LeanToLambdaBox.ErasureCtx.coh_constants
#print axioms LeanToLambdaBox.ErasureCtx.coh_natPeano

-- WHAT THE SLICE BUYS, machine-checked rather than asserted: guard (i''') in
-- `VisitExprRefines.lean`'s NonVacuity section derives the core's erasure conjunct at an
-- ARBITRARY block-local `Γ₀.withFixvars fv`, with `hΓ` discharged by `rfl` and `RunConclδ`
-- still at `Γ₀` — the exact instantiation step 6's recursive exit needs, and the exact
-- thing the two refutation theorems below show a fixed-`Γ` motive cannot supply. The four
-- premise bundles in that guard are the ambient ones, unchanged; only `Γ` moved.
--
-- The obstruction guards stay TRUE theorems: they are now the record of why the fixed-`Γ`
-- motives could not walk the exit, and the check that the `hΓ` binder is load-bearing.
#print axioms LeanToLambdaBox.bridgeInv_blockReader_refuted
#print axioms LeanToLambdaBox.bridgeInv_rec_exit_reader_refuted
#print axioms LeanToLambdaBox.supported_const_fixOpen_not_ambient

-- Stability, once more: the core, its corollary, the block instance, and the crown four.
#print axioms LeanToLambdaBox.visitExpr_refines_erases_core
#print axioms LeanToLambdaBox.visitExpr_refines_erases
#print axioms LeanToLambdaBox.visitExpr_refines_erases_block
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart

-- ============================================================================
-- SLICE Γ-W2 — the block bundle, and the fetch that names the declaration
--
-- (a) THE `decl_run` RELAXATION — the eighth item on the price list, and the one Γ-W0's
-- measurement forced. The conjunct `ci.all = [n]` becomes
--
--     ∃ ci m, r = some ci ∧ ci.all = [m] ∧ remove_unsafe_rec m = n ∧ ci.levelParams = Us
--
-- because `Compiler.LCNF.getDeclInfo?` tries `n._unsafe_rec` first and, at this toolchain,
-- succeeds for every arithmetic declaration the §H benchmarks drag in. At `ci.all = [n]`
-- the field was FALSE at exactly those names — the fragment could not contain them — so
-- this is a repair, not a weakening. Nothing else moves: the run's own test is
-- `ci.all.length == 1`, so the single-declaration prefix is entered either way and step
-- 6's `isFalse` refutation is the same `simp [hall]`; only the `obtain` gains two
-- components.
--
-- A δ-D8e PREDICTION, FALSIFIED. `rec_exit_registers_stripped_name` was read as buying a
-- further FRAGMENT restriction, `remove_unsafe_rec n = n` for every `known n`, to be paid
-- as a field of the block bundle. The arrow was backwards: the caller's `n` is the plain
-- name, and what carries the suffix is the fetched `ci.all`, which the old conjunct
-- wrongly pinned to `n`. Under the relaxation the registration is under
-- `ci.all.map remove_unsafe_rec = [n]` and NO fragment restriction is bought. The negative
-- theorem stays (retitled); `rec_exit_registers_name` is the positive half, decided on the
-- same `f._unsafe_rec` data.
#print axioms LeanToLambdaBox.rec_exit_registers_stripped_name
#print axioms LeanToLambdaBox.rec_exit_registers_name

-- (b) THE BLOCK BUNDLE. `BlockHyps` — the companion of `DeltaHyps`, keyed on the recursive
-- exit's own two runs (`getConstInfo`, `prepare_erasure`) rather than on the declaration
-- fetch, which is why none of `DeltaHyps`' run-keyed clauses can fire inside the block.
--
-- THE KEYING IS THE FINDING. Every run-keyed field reads `known (remove_unsafe_rec m)`,
-- not `known m`: the loop's `m` ranges over `ci.all`, which Γ-W0 measured to be the
-- `._unsafe_rec` names, while the fragment holds the plain ones. Keyed the design's way
-- the bundle would be VACUOUSLY satisfiable at exactly the data the slice exists for.
-- `gBlockKeying` decides both halves on the fixture's real shape.
--
-- SEVEN FIELDS BECAME FIVE, AND FOUR OF THE DROPPED ONES ARE THEOREMS. The design listed
-- `stripped`, `block_lparams`, `block_esrc`, `block_prepared`, `block_shape`, `strengthen`,
-- `nonest`. What ships is `block_lparams`, `block_esrc`, `block_lam`, `strengthen`,
-- `nonest`, because:
--   * `stripped` — dissolved by (a) above;
--   * `block_prepared` — `DeltaHyps.prepared` is keyed on ANY `prepare_erasure` run
--     producing `pe` plus `Esrc n = some pe`, and the block loop holds both (the second
--     from `block_esrc`). It fires unchanged;
--   * `block_shape`'s `NoProj` and empty-context translation — `DeltaHyps.esrc_shape`,
--     verbatim, keyed on `Esrc n = some pe` alone;
--   * `block_shape`'s closedness and fvar-freeness — read off that witness
--     (`TrExprS.closed`, `TrExprS.fvarsIn`), which is what `esrc_shape`'s own docstring has
--     said since δ-D7b.
-- Only λ-headedness survives as an assumption, and it survives because no `TrExprS`
-- witness implies it. `BlockHyps.sibling_scope` is the composition, stated as one theorem
-- so that the division of labour between the two bundles is machine-checked: if a conjunct
-- there ever stops being derivable, that is the line that breaks.
--
-- ALSO DROPPED: the `gw` parameter the design gave the structure. No field mentions a
-- generator — `ci_run` and `prep_run` already live in `DeltaHyps` and the block's
-- `mkFreshFVarId` is `BridgeHyps.fresh_run`'s business — so the bundle is
-- generator-free.
#print axioms LeanToLambdaBox.BlockHyps.of_bot
#print axioms LeanToLambdaBox.BlockHyps.sibling_scope

-- (c) NON-VACUITY, IN THE SAME COMMIT AS THE STRUCTURE — the S1e mitigation the design
-- names explicitly ("land the non-empty instance in the same commit", which is what S1d did
-- not do and paid +776/-269 for). `gBlockHyps` builds the bundle at the recursion fixture
-- `ΓfixRec` with the fragment `{f}` and `Esrc` recording `fixRecSrc`; the one genuine scope
-- field, `block_lam`, is DISCHARGED there rather than assumed, and `gBlockLam_nonvacuous`
-- checks it has something to say. The two run clauses and the two residues stay
-- hypothetical, for the reasons their own docstrings give.
#print axioms LeanToLambdaBox.gBlockKeying
#print axioms LeanToLambdaBox.gBlockHyps
#print axioms LeanToLambdaBox.gBlockLam_nonvacuous

-- (d) THE LAYERING FIX — the obstruction slice Γ-W0 discovered and could only record.
-- Step 6 must call `erases_rec_block_of_run`, `blockMap_getElem?_inv` and
-- `closeFix_eq_block_fold`, and all three lived in `ColdStartDelta.lean`, which is
-- STRICTLY DOWNSTREAM of `VisitExprRefines.lean`:
--
--     VisitExprRefines → EnvErasureNonrec → EnvErasureRec → ColdStartDelta
--
-- Three options were priced against the real import graph before anything moved.
--
--   (a) MOVE the lemmas below the bridge. 614 lines relocated, 0 added, 2 one-line
--       imports, 0 consumer edits, no cycle. TAKEN.
--   (b) SPLIT `VisitExprRefines` (3262 lines; the induction core is 1306-2715, and 37 of
--       the 61 prelude declarations are used directly by it, so the cut is 1305/1957).
--       INFEASIBLE ON ITS OWN: for the core to sit below the four lemmas, `EnvErasureNonrec`
--       and `ColdStartShape` would have to sit below `ColdStartDelta`, which is what
--       `ColdStartDelta` is built on — a cycle. (b) is therefore (a) PLUS a 1957-line split,
--       strictly dominated.
--   (c) HYPOTHESIS FORM, on the `run_visitMutual_ok` vE-generalisation precedent
--       (`ErasureRun.lean`: "in Hoare form the same lemma serves both the inline and the
--       standalone use"). All four facts ARE phrasable in `VisitExprRefines`' scope — only
--       `KeysDistinct` is out of scope, and it inlines to `List.Pairwise` + `Kername.beq`.
--       But ~85 lines of premise would propagate from the core through
--       `visitExpr_refines_erases{,_block}` to `ShippingCorrect`, `ShippingCorrectData`,
--       `FirstOrderShippingIota` and `EnvErasureNonrec` — four capstone-class theorems
--       turning conditional — and the four in-file non-vacuity guards could not discharge
--       them at all, weakening the joint-satisfiability story. Kept as the fallback that
--       cannot fail; not needed.
--
-- WHY (a) IS CHEAP, which is the finding. The entire proof cone of `erases_fix_of_open_nil`
-- — `substFix_mkLambdas`, `Erases.instFixvars`, `hasFVar_mkLambdas`, `erases_target_fvars`,
-- `erases_fix_of_closed` — references NOTHING from `EnvErasureNonrec` or from any `Cold*`
-- module. It lives on `FixUnfold`, `ErasesStrengthen`, `Closed`, `Abstract`, `Erases`,
-- `FixMetatheory`, `ErasureContext` — every one already in `VisitExprRefines`' import
-- closure. `EnvErasureRec` was downstream only because its Part 3 needs
-- `EnvErasureNonrec.RegisteredClosure`. `blockMap_getElem?_inv` is pure Std/List.
-- So `RecBlockErasure.lean` adds ZERO modules to the closure; it re-slices existing ones.
--
-- ONE CORRECTION TO THE BRIEF: `recEnvConsistent_of_block` is NOT a step-6 input and did
-- not move. Step 6's motive-6 conclusion is a `RunConclδ`, whose recursive extension step
-- is `DeltaHyps.RunConclδ.recBlock` — upstream already, and fed by
-- `erases_rec_block_of_run`'s conclusion. `RecEnvConsistent` is capstone-level; leaving it
-- downstream leaves `KeysDistinct` and `ColdStartShape`'s env-lookup kit downstream too,
-- which is where the remaining risk of the move would have lived.
--
-- The move is VERBATIM: every name, statement and proof unchanged, no consumer edited,
-- `EnvErasureRec` and `ColdStartDelta` re-acquiring the names transitively. The entries
-- below are the moved theorems, re-run from their new home.
#print axioms LeanToLambdaBox.Erases.instFixvars
#print axioms LeanToLambdaBox.erases_target_fvars
#print axioms LeanToLambdaBox.erases_fix_of_closed
#print axioms LeanToLambdaBox.erases_fix_of_open_nil
#print axioms LeanToLambdaBox.erases_fix_of_open
#print axioms LeanToLambdaBox.blockMap_getElem?_inv
#print axioms LeanToLambdaBox.closeFix_eq_block_fold
#print axioms LeanToLambdaBox.erases_rec_block_of_run

-- …and the two that stayed, still proving from their new-home dependencies.
#print axioms LeanToLambdaBox.run_rec_exit_siblings_close
#print axioms LeanToLambdaBox.recEnvConsistent_of_block

--------------------------------------------------------------------------------
-- SLICE Γ-W3 — step 6 walks the recursive exit
--------------------------------------------------------------------------------
-- (a) THE OUTPUT-SHAPE OBSTRUCTION, and the design claim it falsifies.
--
-- The design's premise ledger for `erases_rec_block_of_run` routed `hoclosed` (each opened
-- block body is de-Bruijn closed) to `ColdStartInduction.visitExpr_noFix_closed`, annotated
-- "no hypotheses". Inside `visitExpr_refines_erases_core` that is unavailable TWICE OVER:
-- `ColdStartInduction` sits downstream of the bridge, and — the substantive half — the
-- eraser at step 6 is the induction's ABSTRACT fixpoint argument `vE`, about which only the
-- motives may be assumed. No motive carries an output shape, and adding one is not a local
-- change: the IH call graph is one SCC (Γ-W1), so `LBClosed` in motive 1 means `LBClosed` in
-- all seventeen content motives, i.e. a second copy of `ColdStartInduction.visitExpr_shape`.
--
-- The fact is instead read off the ONE thing the motive does hand back — the `Erases`
-- derivation. Erasure moves de-Bruijn indices but never invents one: `Erases.bvar` copies
-- the source's index, every binder rule extends `Δ` exactly where its target extends scope,
-- and the two fix leaves carry `hshift`, which `lbClosed_of_shift_eq` reads back as
-- closedness. That converse is the closedness twin of
-- `FixUnfold.not_hasFVar_of_toBvar_eq_self`, which reads `htobv` the same way — and the
-- parallel is exact, down to which premise of `Erases.const_fix`/`Erases.fix` is consumed.
--
-- All three are pure target-side / relation-side reasoning, hence sorryAx-free.
#print axioms LeanToLambdaBox.lbClosed_of_shift_eq
#print axioms LeanToLambdaBox.LBClosed.mkLambdas_inv
#print axioms LeanToLambdaBox.erases_target_lbClosed

-- …and the `mkDef` output fact `Erases.fix`'s `hrarg` needs. `run_mkDef_ok` had four
-- conjuncts and three destructuring call sites; the fifth fact is stated apart so those are
-- untouched.
#print axioms Erasure.run_mkDef_rarg

-- (b) THE WALK ITSELF. `rec_exit_refines_erases` takes the recursive exit's run at an
-- ABSTRACT eraser together with that eraser's motive-1 refinement hypothesis — which is
-- exactly the shape step 6 of `visitExpr_refines_erases_core` holds — and derives all
-- three conjuncts of `visitMutual`'s motive. Everything the design listed as W3 content is
-- discharged: the id loop (`run_mkFreshFVarId_list`, whose `Nodup` output feeds both block
-- lookups), the chained sibling loop (`run_rec_exit_siblings_chained`), the per-sibling
-- `BridgeInv` rebuild at the block-local `Γ₀.withFixvars fv` (`BridgeInv.withFixvars` +
-- `ErasureCtx.coh_withFixvars` + `BlockHyps.block_lparams`), the erasure IH invoked THERE
-- (Γ-W1's instantiation, guard (i''')), `Supported.withFixvars`, the `Δ → []`
-- strengthening (`Erases.strengthen_fvlift` against `BlockHyps.strengthen`),
-- `erases_rec_block_of_run`, `RunConclδ.recBlock`, and the registration conclusion
-- (`Erasure.recConstState_get?`).
--
-- Its axiom set is a SUBSET of the core theorem's: no `sorryAx`, and the three
-- `Persistent*` modeling axioms it inherits are the ones every run-lemma consumer carries.
#print axioms LeanToLambdaBox.ErasureCtx.coh_withFixvars
#print axioms Erasure.recConstState_get?
#print axioms LeanToLambdaBox.rec_exit_refines_erases

-- (c) AND THE ONE PREMISE THAT DID NOT FALL, with its refutation.
--
-- `hreg` — "`Γ₀` records *this* block for each of its own names" — is `Erases.fix`'s own
-- registration premise. `Γ₀` is fixed before the run builds `defs`, which
-- `ColdStartDelta`'s ledger already called irreducible AT A PARAMETER `Γ`; Γ-W3 confirms
-- it one level further in. Inside the induction the eraser is the abstract fixpoint
-- argument, so any premise pinning the block must quantify over it — and every such
-- phrasing is CONTRADICTORY, not merely strong: two erasers hand back two different
-- blocks and `Γ₀.recBodies` records one. A `BlockHyps` field of that shape would be
-- vacuously satisfiable exactly where the slice needs it, which is the S1d/S1e failure
-- mode the repo priced at +776/−269. So it stays an explicit hypothesis of the walk,
-- discharged by a caller who holds a concrete run.
--
-- TWO DESIGN ROWS FALSIFIED on the way, both about where a fact comes from:
--   * `hoclosed` was routed to `ColdStartInduction.visitExpr_noFix_closed`, "no
--     hypotheses". Unavailable twice over inside the induction — wrong layer, and no
--     motive carries an output shape. Replaced by `erases_target_lbClosed` (Γ-W3a);
--   * `hrarg` was assumed to come from `Erasure.run_mkDef_ok`, which does not state it.
--     `Erasure.run_mkDef_rarg` does (Γ-W3a).
#print axioms LeanToLambdaBox.rec_exit_agreement_eraser_quantified_refuted
#print axioms LeanToLambdaBox.rec_exit_block_ne_of_body_ne

-- (d) THE MOVE. `lbClosed_toBvar` and the binder-closing folds lived in `OutputShape.lean`,
-- which sits below `ErasesCorrectData` and is imported only by `ColdStartInduction` — i.e.
-- strictly downstream of the bridge, the same layering objection Γ-W2c met. Relocated
-- verbatim into `Closed.lean` (which gains one import, `Abstract`, already in the bridge's
-- closure), so `OutputShape` re-acquires them transitively and no consumer moves.
#print axioms LeanToLambdaBox.lbClosed_toBvar
#print axioms LeanToLambdaBox.lbClosed_foldl_zipIdx
#print axioms LeanToLambdaBox.lbClosed_fix_of_bodies

-- (e) AND THE ROUTE THAT WOULD DISSOLVE `hreg`, recorded because it is now the only one.
-- Keyed on the block loop at the SHIPPING `Erasure.visitExpr`, `hreg` is satisfiable — it
-- is the premise `EnvErasureRec.RegisteredClosureRec` has always carried. What blocks step
-- 6 is only that its eraser is abstract. Teaching the motives that the abstract eraser's
-- successful runs are the fixpoint's — a conjunct admissible in exactly the
-- `eraseM_admissible_ok₁` sense, whose eighteen step obligations are the componentwise
-- monotonicity of the erasure functional, available as
-- `Erasure.visitExpr.mutual._proof_1 : Lean.Order.monotone …` — is a second Γ-W1-shaped
-- pass plus order-theoretic plumbing. Priced in `ColdStart`'s residue-1 row; not attempted
-- here.

-- ============================================================================
-- Projection round, slice P3: the first constructed `TrProj` (`ProjPattern.lean`).
--
-- Nobody — upstream or downstream — had ever CONSTRUCTED a `TrProj env U Γ S i e e'`.
-- Every downstream statement about projections was therefore possibly vacuous, and the
-- nine-slice projection round is staked on the answer. It is now settled in the
-- affirmative, at two shapes and both polarities.
--
-- These are CONSTRUCTED guards on a synthetic `VEnv` built with `VEnv.addPat`, so — as
-- for `envι_iota_fires` — they must be **sorryAx-free**, and they are: `[propext,
-- Classical.choice, Quot.sound]`, the ambient set of the `simp` calls in the
-- `constants`-lookup lemmas. No `VEnv.WF` is claimed; `VEnv.Ordered` has no `addPat`
-- clause and `addInduct_WF` is `sorry` upstream, which is why these are `addPat`-built
-- and not `addInduct`-built.
--
-- WHAT THE CONSTRUCTION COST, i.e. the recipe for slices P4-P7: five of `TrProj`'s six
-- conjuncts are `rfl`, `VEnv.addPat_self` and `by simp`. The whole cost is
-- `∃ A, env.HasType U Γ e' A`, and inside it the whole cost is ONE conversion — the
-- recursor's minor premise wants `∀ f̄, motive (mk params f̄)` while the field selector
-- naturally has `∀ f̄, fieldTys[i]`, and a CONSTANT motive makes the two definitionally
-- equal by a single β step under `forallEDF` congruences (`hconvP`/`hconvQ`).
--
-- AND THE LINE IT DRAWS (survey item R2, answered): the constant motive works iff
-- `fieldTys[i]` does not mention the field binders `f₀ … f_{i-1}`. So field 0 of ANY
-- structure — dependent or not — is as easy as this file, and so is every typeclass
-- method; a field i > 0 whose type genuinely depends on an earlier field (`Sigma.snd`)
-- needs the motive `fun p => β p.0`, i.e. β PLUS a firing of the ι rule. That case is
-- inhabitable by the same kit and is NOT attempted here — the round's one residue on
-- this axis, and a narrow one.
-- ============================================================================
-- Positive, at `MyProd` (np = 1, one ctor, TWO fields, no indices): both fields, at a
-- variable discriminant and at a saturated constructor spine. Two fields so that
-- `VExpr.fieldSelector`'s `Fs.length - 1 - i` convention is exercised rather than
-- degenerate (`selP_zero`/`selP_one` pin it by `rfl`).
#print axioms LeanToLambdaBox.selP_zero
#print axioms LeanToLambdaBox.selP_one
#print axioms LeanToLambdaBox.trProjP_bvar0
#print axioms LeanToLambdaBox.trProjP_bvar1
#print axioms LeanToLambdaBox.trProjP_ctor0
#print axioms LeanToLambdaBox.trProjP_ctor1
-- The second half of the kill-check: `TrExprS` at a real `Expr.proj`, over those
-- witnesses — `DeltaHyps.prepared`'s second conjunct in miniature, the conjunct the
-- projection round exists to make satisfiable. `_ctor` has a compound discriminant, so
-- `TrExprS.proj`'s first premise is doing work rather than being a variable lookup.
#print axioms LeanToLambdaBox.trExprSP_proj_bvar
#print axioms LeanToLambdaBox.trExprSP_proj_ctor
-- Positive, at the PAYOFF shape `MyOfNat` (np = 2, one field): the type-class shape the
-- design's `OfNat.ofNat` trace runs through, where `params` is a two-element list so the
-- `params ++ [motive, selector, major]` append is not degenerate.
#print axioms LeanToLambdaBox.trProjQ_bvar
#print axioms LeanToLambdaBox.trExprSQ_proj
-- Negative: at a `pats`-free environment `TrProj` is uninhabited, so the witnesses above
-- are about the registration and not artefacts of a degenerate definition.
#print axioms LeanToLambdaBox.trProj_refuted
#print axioms LeanToLambdaBox.trProj_refuted_empty

-- ============================================================================
-- SLICE Γ-W3.5 — THE APPROXIMATION CONJUNCT, AND THE WALL BEHIND THE WALL
-- ============================================================================
--
-- Γ-W3c priced a route out of the one premise `rec_exit_refines_erases` leaves standing.
-- This slice paid it. Three things to check here: that the toolkit is clean, that the
-- crown theorems did not move, and that the walk's own axiom set did not grow.
--
-- (a) THE TOOLKIT. `⊑` is `partial_fixpoint`'s own order on `EraseM`. `run_ok_of_le` is
--     the only direction the bridge consumes — below the fixpoint a *successful* run is
--     the fixpoint's run, verbatim — and it is also the correction to Γ-W3c's wording:
--     the conjunct CANNOT be the run-ok implication that slice named. Run-ok agreement is
--     strictly weaker than `⊑` (`EST.bot` is an `.error`, so an eraser that errors where
--     the fixpoint succeeds satisfies it) and the erasure functional does not preserve
--     it; monotonicity gives `F x ⊑ F y` from `x ⊑ y` and there is no run-ok analogue to
--     feed. So the motives carry `⊑`, and run-ok is its corollary.
--
--     `admissible_and_le` is why the eighteen admissibility obligations cost nothing: a
--     chain below the fixpoint has its supremum below it (`CCPO.csup_le`), and Γ-W3c's
--     other reading — that the new conjunct's `Q` does not mention `f` — holds.
--     `fix_step_le` is `Lean.Order.fix_eq` read as an inequality, and `mutual_le_of`
--     packs the step's eighteen hypotheses into the `PProd` chain
--     `Erasure.visitExpr.mutual` inhabits, so that
--     `Erasure.visitExpr.mutual._proof_1 : Lean.Order.monotone …` — the monotonicity proof
--     `partial_fixpoint` generated for the erasure family itself — discharges each step
--     obligation with one projection. Nothing here is a conjecture and nothing is new
--     mathematics; the eighteen `_eq_mutual` slot equations exist only because
--     `partial_fixpoint` seals each member behind an `@[irreducible] def`.
#print axioms Erasure.approx_rfl
#print axioms Erasure.run_ok_of_le
#print axioms Erasure.run_ok_of_le₁
#print axioms Erasure.admissible_and_le
#print axioms Erasure.fix_step_le
#print axioms Erasure.visitExpr_eq_mutual
#print axioms Erasure.visitAlt_eq_mutual
#print axioms Erasure.mutual_le_of
-- (b) THE TRANSPORT. `⊑` travels under the recursive exit's sibling `mapM` by
--     `List.monotone_mapM` and `Erasure.withReader_mono` alone — no fact about the
--     erasure family is needed, only that the eraser occurs positively in the loop body.
--     That is what lets a walk at an ABSTRACT eraser feed a premise stated at the
--     SHIPPING one.
#print axioms Erasure.rec_exit_siblings_mono
#print axioms Erasure.run_rec_exit_siblings_le
-- (c) THE CROWN FOUR DID NOT MOVE. Both bridge theorems keep the same seven axioms they
--     had at Γ-W3c — `propext`, `Classical.choice`, `Quot.sound` and lean4lean's four
--     modeling axioms — and `visitExpr_refines_erases`' STATEMENT is byte-identical: the
--     new conjunct is a tautology at the fixpoint, so the export projects one `.1`
--     further and nothing else changed. `rec_exit_refines_erases` keeps its six, a subset.
#print axioms LeanToLambdaBox.visitExpr_refines_erases_core
#print axioms LeanToLambdaBox.visitExpr_refines_erases
#print axioms LeanToLambdaBox.rec_exit_refines_erases
--
-- (d) WHAT THE SLICE BOUGHT, AND WHAT IT DID NOT — the honest half.
--
--     BOUGHT. `hreg` used to be stated at the induction's abstract eraser, where every
--     phrasing is *contradictory*: two erasers hand back two blocks and `Γ₀.recBodies`
--     records one (`rec_exit_agreement_eraser_quantified_refuted`, with
--     `rec_exit_block_ne_of_body_ne` as its instance on real leaves). It is now
--     `RecBlockRegistered`, keyed on `Erasure.visitExpr`, where there is one block per
--     `(names, ids, ctx, s₀, wi)`. Guard (iv'') is the fixture Γ-W3 could not state: the
--     walk fires at exactly the data step 6 holds — an abstract eraser, its motive-1
--     PAIR, and the shipping-keyed premise. Guard (iv') is the same composition at the
--     induction's conclusion, where the approximation half is trivial.
--
--     NOT BOUGHT. Step 6 still refutes the recursive exit, and `DeltaHyps.nonrecursive`
--     (scope restriction 5) stands. The obstruction is a DIFFERENT quantifier and this is
--     the first slice that can name it: `hreg` is stated at *a* reader and *a* state, and
--     step 6's motive quantifies both, so a bundle-level premise would have to quantify
--     them too. Unlike the eraser quantification that premise is not provably
--     contradictory — there is only one eraser now, so the two-blocks argument has
--     nothing to run on — but it is not SUPPLIABLE either: readers differing in
--     `Erasure.Config` erase the same block to different `defs`, the only reader/`Γ₀`
--     coherence available at this level is `BridgeInv.natcfg` and that is
--     one-directional, and a caller who built `Γ₀` by running the eraser holds one reader
--     and one state rather than all of them. A `DeltaHyps` field of that shape was
--     written, compiled and REVERTED in this slice for exactly that reason: it would have
--     been the S1d/S1e failure mode with `ctx` in the role `known` played there — a
--     premise vacuously satisfiable precisely where the slice needs it. The measurement
--     is recorded rather than the field.

-- ============================================================================
-- SLICE Γ-W3.6a — THE CONFIG GATE
-- ============================================================================
--
-- The measurement Γ-W3.5 recorded above named a *reader/state* quantifier as what keeps
-- step 6's recursive branch closed. This slice takes the reader half of it apart, and the
-- finding is that only one field of the reader was ever at issue.
--
-- (a) CONFIG IS A RUN INVARIANT, AND NOW THE INVARIANT SAYS SO. `ErasureContext` has four
--     fields. Of the five `withReader` sites in the shipping eraser — `withLocalDecl`,
--     `withLocalDef`, `visitMutual`'s non-recursive exit, its block entry, its per-sibling
--     loop — not one touches `config`; `{ … with config := … }` occurs nowhere in the
--     eraser; `ReaderT.adapt`/`withTheReader` are never used; and the only reader built
--     from scratch is `Erasure.run`'s `{ config }`. So `BridgeInv.cfg : ctx.config = cfg₀`
--     costs five transport lines and ten construction sites, eight of them `rfl`, and
--     ZERO changes at the transport application sites — the field travels wherever the
--     invariant does. `BridgeInv.withFixvars` already demanded `hcfg : ctx'.config =
--     ctx.config` for `natcfg`, supplied by `rfl` at both of its call sites, so the fully
--     general reader is pinned there too.
#print axioms LeanToLambdaBox.BridgeInv
#print axioms LeanToLambdaBox.BridgeInv.mono
#print axioms LeanToLambdaBox.BridgeInv.mono_state
#print axioms LeanToLambdaBox.BridgeInv.withFixvars
#print axioms LeanToLambdaBox.BridgeInv.mkLocalDecl
#print axioms LeanToLambdaBox.BridgeInv.mkLetDecl
#print axioms LeanToLambdaBox.gBridgeInv_nil
--
-- (b) THE FIX-ONCE BONUS. Two SHIPPED fields carry the same defect the Γ-W3.5 objection
--     names, and they carried it since Γ-W2: `DeltaHyps.prep_esrc` and
--     `BlockHyps.block_esrc` quantify the reader of a `prepare_erasure` run and pin its
--     OUTPUT to a value fixed before the run — while that output demonstrably depends on
--     `ctx.config.csimp`. Ungated, the clause identifies the bodies two configs prepare,
--     which for an `Esrc` that distinguishes them is contradictory. Both are now gated on
--     `ctx.config = cfg₀`, the bundles carrying `cfg₀` as a parameter. This STRENGTHENS
--     the fields (they say less), so every consumer keeps working: each holds a
--     `BridgeInv` and reads the equation off `BridgeInv.cfg`, with
--     `RecBlockErasure.blockReader_config` (`rfl`) covering the block loop's reader.
#print axioms LeanToLambdaBox.DeltaHyps
#print axioms LeanToLambdaBox.DeltaHyps.of_bot
#print axioms LeanToLambdaBox.BlockHyps
#print axioms LeanToLambdaBox.BlockHyps.of_bot
#print axioms LeanToLambdaBox.BlockHyps.sibling_scope
#print axioms LeanToLambdaBox.gBlockHyps
--
-- (c) WHAT THE `∀ ids` QUANTIFIER COSTS: NOTHING, AND HERE IS THE MEASUREMENT.
--     `RecBlockRegistered` quantifies the block's fresh ids. They do not survive into the
--     block it speaks about: `erases_target_fvars` says an fvar-free source erases to a
--     target whose free variables are fixvars of the context (`Erases.fvar` is the only
--     rule that can invent one and its source-side premise is `False`), and
--     `not_hasFVar_closeFix` says `mkDef`'s fold abstracts exactly those. So the stored
--     body is `FVarId`-free.
--
--     What this does NOT buy — and the reason the premise stays an assumption rather than
--     becoming a theorem — is equivariance: "no id occurs in the output" is not "two runs
--     from different generator states build the same output", which would need a renaming
--     induction over the whole eighteen-motive family. And the premise's world quantifier
--     ranges over Core environments, so no such theorem exists to be had at all.
#print axioms LeanToLambdaBox.rec_exit_block_fvar_free
--
-- (d) THE CROWN DID NOT MOVE. Both bridge theorems keep the seven axioms they had at
--     Γ-W3.5 — `propext`, `Classical.choice`, `Quot.sound` and lean4lean's four modeling
--     axioms — and `rec_exit_refines_erases` keeps its six. A parameter and a `rfl`-valued
--     field add nothing.
#print axioms LeanToLambdaBox.visitExpr_refines_erases_core
#print axioms LeanToLambdaBox.visitExpr_refines_erases
#print axioms LeanToLambdaBox.visitExpr_refines_erases_block
#print axioms LeanToLambdaBox.rec_exit_refines_erases

-- ============================================================================
-- SLICE Γ-W3.6b — THE TRADE, AND THE WALK
-- ============================================================================
--
-- The recursion wall's last brick. `DeltaHyps.nonrecursive` is DELETED and the bridge's
-- step 6 WALKS `visitMutual`'s recursive exit; the `absurd` is gone.
--
-- (a) THE PREMISE. `RecBlockAgreement` is `Erases.fix`'s own registration premise, stated
--     over the configurations the induction quantifies. It is not a theorem — `Γ₀` is
--     fixed before the run builds `defs` — but its quantifiers are GATED, and that is the
--     whole content of the slice: on the fragment (`known (remove_unsafe_rec m)` plus
--     `Nodup`, keyed as `BlockHyps` is), and on `BridgeInv`, whose `cfg` field pins the
--     config (Γ-W3.6a) and whose `consts`/`knames` pin the registry. The two refutations
--     anyone could write — two configs, one non-canonical registry — are therefore closed
--     rather than assumed away. What is left free is `ctx.lctx`, `s.inductives` and the
--     world, which is exactly what `DeltaHyps.prep_esrc`, `BlockHyps.block_esrc` and
--     `BridgeHyps.fresh_run` have carried since they shipped.
#print axioms LeanToLambdaBox.RecBlockAgreement
#print axioms LeanToLambdaBox.RecBlockAgreement.of_bot
#print axioms LeanToLambdaBox.gRecAgreement
--
-- (b) THE NEGATIVE RECORD STANDS, AND IS NOW LABELLED. The eraser-quantified phrasing is
--     still refuted, with its exhibited instance on real leaves; that is why the premise is
--     keyed on `Erasure.visitExpr`. The READER-quantified refutation — "two configs, two
--     blocks" — is the one that would have applied to `RecBlockAgreement`, and it cannot be
--     instantiated any more: `BridgeInv.cfg` admits one config. Closed by the gate, not
--     withdrawn.
#print axioms LeanToLambdaBox.rec_exit_agreement_eraser_quantified_refuted
#print axioms LeanToLambdaBox.rec_exit_block_ne_of_body_ne
#print axioms LeanToLambdaBox.bridgeInv_blockReader_refuted
#print axioms LeanToLambdaBox.bridgeInv_rec_exit_reader_refuted
--
-- (c) THE TRADE, AS A COUNT. `DeltaHyps` loses one field and one scope restriction (five
--     become four): a recursive fragment constant is no longer excluded. What replaces it
--     is two premises of the bridge — `Hβ : BlockHyps` (which the walk needed anyway) and
--     `Hreg` — both of the `block_esrc` class, and at `known = ⊥` `Hreg` is a theorem, so
--     the block instantiation `visitExpr_refines_erases_block` picks it up for free.
#print axioms LeanToLambdaBox.DeltaHyps
#print axioms LeanToLambdaBox.DeltaHyps.of_bot
#print axioms LeanToLambdaBox.BlockHyps.of_bot
--
-- (d) THE CROWN, AGAIN. Two premises and a deleted field change no axiom set. Both bridge
--     theorems keep their seven, `rec_exit_refines_erases` its six, and the capstones are
--     verbatim what they were — they gained `Hβ`/`Hreg` as premises, which is a widening of
--     the hypothesis list, not of the trust base.
#print axioms LeanToLambdaBox.visitExpr_refines_erases_core
#print axioms LeanToLambdaBox.visitExpr_refines_erases
#print axioms LeanToLambdaBox.visitExpr_refines_erases_block
#print axioms LeanToLambdaBox.rec_exit_refines_erases
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart

-- ============================================================================
-- Projection round, slices P0 / P1 / P4 (2026-08-27).
--
-- P3 settled that `TrProj` is inhabited. These three slices build the model on top of
-- it: a `Γ` column, an `Erases` rule, and the upstream interface. THE ROUND ADDS NO
-- AXIOM AND NO `sorryAx`. Every declaration below measures either `[propext]` or the
-- three standard axioms, and the crown four did not move — `visitExpr_refines_erases`
-- and `_core` keep their seven, `rec_exit_refines_erases` its six.
--
-- (a) P0 — THE COLUMN, AND THE DE-OPACIFICATION.
--
--     `ErasureCtx.projs` is the one datum `visitProj` reads that no other field
--     supplies: `Expr.proj S i e` names only the STRUCTURE TYPE, while `ctorArities` is
--     keyed on the constructor and `casesOns` is populated only when the walk saw a
--     `casesOn` — which a projection-only structure never produces.
--
--     `NoFix` and `NoBlock` stopped being `True` at `.proj`. The stated reason for the
--     opaque clause covered `.construct` only; `.proj` was unreachable because `Erases`
--     had no rule. It has one now, and `NoFix (.proj p t) = True` would hide a `.fix`
--     under a projection from the very exclusion the data simulation runs on. The
--     forced conclusion-position repairs numbered FOUR, not the ~20 the design
--     predicted, because the `.proj` arms of the `LBClosed` inductions were already
--     recursive; one of the four is in `ColdStartInduction.lean`, which is the round's
--     only edit outside its own lane.
--
--     The env records are `ErasesEnvCases`' transposes, and `ProjFieldsCoherent` is
--     `CtorFieldsCoherent`'s twin keyed on `projs` — a twin rather than a widened
--     hypothesis, so the original's six call sites stay byte-identical. All discharged
--     from registration and guarded at `AC`, which is literally the `is_struct` shape —
--     and guarded on the SAME `Γproj` the model-side rule guards use, so `projInd`
--     (the `InductiveId` in the emitted `ProjectionInfo`) and `acIid` (the one `acΓ`
--     registers) are demonstrably one inductive, by `rfl`.
#print axioms LeanToLambdaBox.ErasesEnvProjs.nonProp
#print axioms LeanToLambdaBox.erasesEnvProjs_of_registeredProjs
#print axioms LeanToLambdaBox.projFieldsCoherent_of_registered
#print axioms LeanToLambdaBox.Γproj_projInd_eq_acIid
#print axioms LeanToLambdaBox.Γproj_registeredProjs
#print axioms LeanToLambdaBox.Γproj_erasesEnvProjs
#print axioms LeanToLambdaBox.Γproj_nonProp
#print axioms LeanToLambdaBox.Γproj_projFieldsCoherent
--
-- (b) P1 — THE RULE. `Erases.proj` reads `visitProj` back off `Γ`, carries ONE
--     sub-derivation, and — deliberately — NO `TrExprS` premise. `box`/`lam`/`letE`
--     carry one because they record a `VExpr` witness that must transport; this rule's
--     target carries none. Adding one would cost an equational-uniqueness obligation
--     that is FALSE at `.proj`: `TrProj` pins `params`/`fieldTys` only up to defeq,
--     which is why `TrProj.uniq` claims `IsDefEqU`.
--
--     Eleven structural arms, all one-liners. The twelfth — `Erases.strengthen_fvlift`
--     — is VACUOUS, its scope predicate being `NoProj`, and that is exactly the wall
--     slice P2 exists to move; the arm records the reason rather than hiding it.
--
--     Guards at both polarities on `Γproj` (one parameter, one field, so `2 = 1 + 1`
--     decomposes non-degenerately): positive at a variable and at a saturated
--     constructor spine, negative as `Erases.proj_none` — at `Γ.projs = ⊥` the only
--     erasure of a projection is `box`.
#print axioms LeanToLambdaBox.Erases.proj_inv
#print axioms LeanToLambdaBox.Erases.proj_none
#print axioms LeanToLambdaBox.erases_proj_fvar
#print axioms LeanToLambdaBox.erases_proj_ctor
#print axioms LeanToLambdaBox.foldl_app_const_ne_proj
#print axioms LeanToLambdaBox.foldl_app_cons_ne_proj
#print axioms LeanToLambdaBox.substFVarList_proj
--
-- (c) P4 — THE INTERFACE, AND WHY IT IS NOT `of_trEnv`.
--
--     `TrEnv.proj_defeq` is still `sorry` at `7a5e96d`, and — this is the finding, and
--     it SURVIVED the motive re-pin, which fixed `TrProj.uniq` and nothing here — it is
--     also missing a hypothesis. Its `hp : TrProj …` carries its own existentially
--     bound constructor name; its `hd` supplies a different, universally quantified one
--     for the spine the discriminant is defeq to; nothing ties them. Since
--     `Pattern.Matches` on `SimplePattern.iota recName _ ctorName' _` matches the major
--     premise against `ctorName'`, the reduction cannot fire without the agreement, and
--     recovering it from `TrEnv` + `HasType` is a canonicity argument rather than a
--     rewrite. So the statement is plausibly UNPROVABLE as written. Escalated as a
--     STATEMENT correction, not a proof request.
--
--     `TrProjCtor` is `TrProj` with that name exposed, and the two conversions below
--     show the exposure is a reparenthesisation, not a strengthening. `ProjDefeqSpec`
--     states the reduction over it; `ProjShape` is the `rfl`-checkable certificate whose
--     `ival.ctors = [ctor]` conjunct supplies the agreement locally.
--
--     `ProjDefeqSpec.of_trEnv` is DELIBERATELY ABSENT. It is one line and
--     `TrProjCtor.toTrProj` is the piece it needs, but calling `TrEnv.proj_defeq` today
--     injects the upstream PROJ-TODO `sorryAx`, and this round adds none. The interface
--     stays a NAMED PREMISE — the `PatsIotaSpec` idiom — so the injection point, when it
--     comes, is one declaration.
#print axioms Lean4Lean.TrProjCtor.toTrProj
#print axioms Lean4Lean.TrProj.exists_ctorName
#print axioms Lean4Lean.TrExprS.proj_inv
#print axioms Lean4Lean.TrExprS.proj_inv'
#print axioms LeanToLambdaBox.ProjShape.ctorAgreement
#print axioms LeanToLambdaBox.trProjCtorP_bvar0
#print axioms LeanToLambdaBox.trProjCtorQ_bvar
#print axioms LeanToLambdaBox.trProjCtor_refuted
--
-- (d) WHAT DID NOT LAND, AND WHY — two rules the slicing said were free and are not.
--
--     `Supported.proj` (planned P1) is NOT independent of P8. Step 1 of
--     `visitExpr_refines_erases_core` analyses `hsupp` by a complete `cases`, so a new
--     alternative of `Supported` is a new arm there, and only MOTIVE 10 can discharge
--     it — and motive 10 concludes `True`. Giving it content needs a `ProjBridgeHyps`
--     bundle and a new premise on the bridge theorem.
--
--     `SEvalDataι.proj` (planned P1) is NOT independent of P6+P7, for the same
--     structural reason at a different relation: THREE complete inductions run over
--     `SEvalDataι` (`SEvalDataι_defeq`, `erases_correct_dataι`,
--     `SEvalDataι_partial_cases_lam_elim`), so a new constructor is three new arms, two
--     of which need `ProjConsistent` threaded through twelve call sites and the full
--     simulation case.
--
--     Both are structural facts about complete case analyses, not proof difficulty, and
--     both mean the round has fewer independent slices than nine. What IS independent
--     and did land is the whole model layer: the column, the rule, the predicates, the
--     env records and the upstream interface.
--
--     `ProjConsistent` is defined (`SourceEvalData.lean`) as the premise those slices
--     will take. It is a `Prop` HYPOTHESIS, never an axiom, and — like `IotaConsistent`
--     — it stays one even once derivable, because that is what keeps `safety`/`kenv`
--     out of the `VEnv`-level statements.

-- ============================================================================
-- SLICE Γ-W4 — `hnorec` DIES; THE RECURSIVE COLD-START CAPSTONE
-- ============================================================================
--
-- The finale of the recursion wall on the capstone side. Γ-W3.6b landed the PRODUCER —
-- step 6 walks `visitMutual`'s recursive exit — and left the CONSUMER half: both
-- cold-start capstones still carried `hnorec : Γ.recBodies = ⊥`, an S-class scope
-- restriction that excluded every recursive program from the statement. It is DELETED.
--
-- (a) WHAT REPLACED IT. One premise, `RecCovered Γ Esrc sf`, stated about the run's final
--     state: every constant `Γ` records as recursive is in the fragment's source
--     environment and has ITS block stored under its kername. It is the CONVERSE of
--     `RecBlockAgreement` — that one reads run → `Γ` (the block a run builds is the block
--     `Γ` records, which is `Erases.fix`'s `hreg`), this one reads `Γ` → run — and neither
--     derives the other: a `Γ` may name a block for a constant the program never calls,
--     and then no walk registers anything for it. So it is premised, of the
--     registration-agreement class, and at `Γ.recBodies = ⊥` it is a THEOREM
--     (`RecCovered.of_noRec`), which is how every `known = ⊥` guard picks it up for free —
--     the mirror of `RecBlockAgreement.of_bot`.
#print axioms LeanToLambdaBox.RecCovered
#print axioms LeanToLambdaBox.RecCovered.of_noRec
--
-- (b) THE CONVERSION, AND WHAT IT COST. `recEnvConsistent_of_deltaMem_walked` is
--     `registeredClosureData_of_deltaMem_walked` with the applied-form conjunct dropped
--     and the coverage agreement added: `hdisj`/`hclenv`/`huni` are the SAME THREE
--     ARGUMENTS a capstone already assembles for its `ErasesEnvDeltaData`, so the
--     recursive record costs exactly one new premise and no new machinery. The `Erases`
--     conjunct is DERIVED — `DeltaMem` is keyed on the recorded entry and says nothing
--     about its shape, so a `.fix` body was inside its statement all along, and the walked
--     exit's `DeltaMem.recBlock` is what puts one there.
--
--     No single-block restriction, unlike `recEnvConsistent_of_block`: the conversion is
--     keyed per name on `Γ.recBodies n`, so a `Γ` describing several blocks costs nothing.
--     What stays single-declaration is the SUBJECT — `Erasure.erase` erases one term.
#print axioms LeanToLambdaBox.recEnvConsistent_of_deltaMem_walked
--
-- (c) SUPPLIABILITY, ON REAL RECURSIVE DATA — the S1d/S1e test, run twice. The premise
--     that replaces a deleted scope restriction must not be one nothing can satisfy.
--     `gRecCoveredD8` computes it on the self-referential fixture `def f (a : Prop) := f a`
--     at the state the walked recursive exit produces; `gDeltaMemRecD8` builds the δ record
--     there through `DeltaMem.recBlock` (the extension step that exit fires) with the
--     `Erases.fix` witness DERIVED by `erases_rec_block_of_run`; and
--     `gRecEnvConsistentWalkedD8` runs the whole conversion end to end at a `Γ` that
--     genuinely registers recursion — `hnest` the only thing left hypothetical.
#print axioms LeanToLambdaBox.gRecCoveredD8
#print axioms LeanToLambdaBox.gDeltaMemRecD8
#print axioms LeanToLambdaBox.gRecEnvConsistentWalkedD8
--
-- (d) THE DELIVERABLE: A COLD-START ENTRY-POINT THEOREM ON A RECURSIVE PROGRAM.
--     `ΓFOrec` grafts the fixture's block onto `ΓFOd`'s nullary constructor, and
--     `ΓFOrec_norec_refuted` is the measurement that makes the guard mean something: the
--     deleted premise is FALSE there, so before this slice no cold-start capstone could
--     speak about that `Γ` at all. The graft is forced, not cosmetic — `FirstOrderValue`
--     has exactly one constructor (`.ctor`), so at a `Γ` registering no constructor the
--     capstone's `hfo` premise is UNINHABITED and no conclusion can be stated.
--
--     `gRecCoveredFO` is the same suppliability check at the guard's own final state.
#print axioms LeanToLambdaBox.ΓFOrec_norec_refuted
#print axioms LeanToLambdaBox.ΓFOrec_cc
#print axioms LeanToLambdaBox.gRecKeysFO
#print axioms LeanToLambdaBox.gRecCoveredFO
--
-- (e) THE VACUITY THE GUARD NEARLY WAS. Its first version ran at `envFO` and proved
--     NOTHING: `DeltaHyps.esrc_shape` demands a `TrExprS` translation of every body the
--     fragment records, `fixRecSrc` mentions `.const f []`, and `envFO` does not declare
--     `f` — so the `Hδ` bundle is UNINHABITABLE there and taking it hypothetically is
--     taking `False`. The fix is the environment: `envRec` declares `f` as an AXIOM of
--     type `Prop → I`, which is the honest modelling (a recursive definition has no kernel
--     defining equation — that is why the eraser fetches `f._unsafe_rec`).
--     `gRecEsrcShape` discharges the field that was unsatisfiable and `gRecScope` the
--     other three fragment-scope fields, so nothing in the bundle is hypothetical because
--     it is empty. This is the S1d/S1e discipline applied from the environment side, and
--     it is the one design claim of this slice that failed on first contact.
#print axioms LeanToLambdaBox.envRec_wf
#print axioms LeanToLambdaBox.envRec_trFixRecSrc
#print axioms LeanToLambdaBox.gRecEsrcShape
#print axioms LeanToLambdaBox.gRecScope
#print axioms LeanToLambdaBox.envRec_foC
--
-- (e') AND ONE PREMISE CAME OUT BETTER THAN PRICED. `hcon : SEnvConsistent` is
--     DISCHARGED at the recursive fixture, by η: the source body `fun (a : Prop) => f a`
--     is `f`'s η-expansion and `VEnv.IsDefEq.eta` is a rule of lean4lean's theory. That is
--     a property of this fixture, not of recursion. The structural fact behind it is worth
--     keeping: a well-formed `VEnv` cannot carry a SELF-REFERENTIAL defining equation,
--     because `VDecl.def` types a constant's value in the environment BEFORE the constant
--     is added. So for a general recursive constant `hcon` is never the `envδ`-style
--     defining-equation discharge — it is a trust item about a constant whose only kernel
--     form is `_unsafe_rec`.
#print axioms LeanToLambdaBox.envRec_senvConsistent
--
-- (f) THE CROWN, ONE LAST TIME. Deleting a premise and adding one changes no axiom set:
--     both capstones are VERBATIM the eight they have carried since the `fee3ada` re-pin
--     (three standard + `sorryAx` + the four `Expr`/`PersistentHashMap` modelling axioms),
--     the bridge keeps its seven and `rec_exit_refines_erases` its six. The `sorryAx` is
--     still unique typing, inherited, and still not ours.
#print axioms LeanToLambdaBox.visitExpr_refines_erases
#print axioms LeanToLambdaBox.rec_exit_refines_erases
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart

-- ============================================================================
-- SLICE proj-P2 — `NoProjBinders`: THE TYPECLASS LAYER STOPS BEING EXCLUDED
-- ============================================================================
--
-- The wall this slice takes down is NOT `Erases` and NOT `TrProj`: since P1 the erasure
-- relation has a `proj` rule and since `fee3ada` `TrProj` is a real, inhabited definition
-- (P3). What still excluded every class method was a SCOPE PREDICATE:
-- `DeltaHyps.esrc_shape` demanded `NoProj pe` of every body the fragment records, and
-- `NoProj (.proj ..) = False`, while `OfNat.ofNat`'s prepared body IS a projection —
-- `fun α x self => self.1`. So the field was uninhabitable for the whole
-- typeclass-dispatch layer no matter what could be derived about it.
--
-- (a) WHERE THE PREDICATE IS ACTUALLY SPENT — the measurement that sizes the slice.
--     `Erases.strengthen_fvlift` THREADS `NoProj` through all sixteen arms but CONSUMES it
--     at exactly three: a boxed subterm (whole), a λ binder's type, and a `let`'s type and
--     value — the three positions where `Erases` records a `VExpr` witness an `FVLift` must
--     match ON THE NOSE. `NoProjBinders` keeps the binder-shaped ones and drops the rest.
#print axioms LeanToLambdaBox.NoProjBinders
#print axioms LeanToLambdaBox.NoProj.toNoProjBinders
#print axioms LeanToLambdaBox.NoProjBinders.toConstructor
#print axioms LeanToLambdaBox.noProjBinders_foldl_app
--
-- (b) THE BOX ARM, RE-PROVED THROUGH DEFEQ. The boxed-subterm position cannot simply be
--     dropped — a boxed proof may itself contain a projection (`And` is a structure) — so
--     it is PAID FOR: `TrExprS.uniq` gives a definitional equality where `TrExprS.unique`
--     gave an equation, and `Erasable.defeq` transports the irrelevance witness along it.
--     That is the module docstring's own "survivable in `box`, fatal in `lam`" split, cashed.
--
--     THE PREMISE COST, AND A DESIGN CLAIM CORRECTED. The design priced this as
--     "`hΔ' : Δ'.FVWF` strengthens to `VLCtx.WF`" and called it free. It is not obviously
--     available: `erases_weakFV`'s docstring records that `VLCtx.WF` CANNOT survive this
--     induction, because the `lam`/`letE` arms descend to `(none, .vlam ty') :: Δ'` and
--     `Erases.lam` carries no `IsType`. It survives HERE for a reason that lemma has no
--     analogue of — `hwt`, the small-context translation, is a premise, and lean4lean's
--     `TrExprS.lam`/`TrExprS.letE` DO record the binder's `IsType`/`HasType`, so the
--     extended context's `VLocalDecl.WF` is that witness weakened along `W.toCtx`.
--     `env.Ordered` also strengthens to `env.WF`. Both are held by every caller already.
#print axioms LeanToLambdaBox.Erases.strengthen_fvlift_binders
--
-- (c) TWO LEMMAS, NOT ONE — and this is the whole trust story of the slice.
--     `TrExprS.uniq` bottoms out in `TrProj.uniq`, still `PROJ-TODO`, so the defeq route
--     carries `sorryAx` where the equational route does not. Rather than move that reach
--     into declarations that were clean, the equational `Erases.strengthen_fvlift` is KEPT
--     verbatim (`NoProj`, `Ordered`, `FVWF`, sorryAx-free) beside the new one, and the two
--     scopes are split by consumer:
--       * `erases_strengthen_closed`/`erases_uniform_closed` take `NoProjBinders` and route
--         through the defeq lemma — they have carried that `sorryAx` since `fee3ada`, so
--         nothing moves;
--       * the bridge's recursive exit keeps the equational lemma, because
--         `BlockHyps.block_lam` keeps `NoProj` for the sibling bodies (below).
--     MEASURED: the whole audit is BYTE-IDENTICAL across this slice, all 750 earlier
--     entries, including `Erases.strengthen_fvlift` (three axioms, no `sorryAx`),
--     `visitExpr_refines_erases` (seven) and `rec_exit_refines_erases` (six).
#print axioms LeanToLambdaBox.Erases.strengthen_fvlift
#print axioms LeanToLambdaBox.erases_strengthen_closed
#print axioms LeanToLambdaBox.erases_uniform_closed
--
-- (d) WHERE THE `NoProj` WENT. `DeltaHyps.esrc_shape` now reads `NoProjBinders`; the
--     strong predicate reappears as the second conjunct of `BlockHyps.block_lam`
--     ("a block source is a projection-free λ"), keyed on the recursive exit's own
--     fragment. NOTHING IS NEWLY ASSUMED: it is the same condition `esrc_shape` demanded
--     of every fragment body before this slice, now demanded only of the recursive ones,
--     and lifting it is a follow-on slice whose price is exactly the axiom movement (c)
--     avoids. `BlockHyps.sibling_scope` is where the two bundles' division of labour is
--     machine-checked, and it is the line that would break.
#print axioms LeanToLambdaBox.BlockHyps.of_bot
#print axioms LeanToLambdaBox.BlockHyps.sibling_scope
#print axioms LeanToLambdaBox.gBlockHyps
#print axioms LeanToLambdaBox.gBlockLam_nonvacuous
#print axioms LeanToLambdaBox.gRecEsrcShape
--
-- (e) NON-VACUITY, BOTH POLARITIES AND BOTH LEVELS — the S1d/S1e discipline, applied to a
--     WEAKENING rather than to a new premise. A weakened scope condition is worthless if
--     it admits nothing new, so the guard is the term the slice exists for:
--       * SYNTACTIC, at the design's full `fun α x self => self.1`:
--         `noProjBinders_ofNatBody` holds and `noProj_ofNatBody_refuted` refutes the old
--         predicate on the same term;
--       * ENVIRONMENT-LEVEL, in `esrc_shape`'s own shape and at the EMPTY context:
--         `gEsrcShapeProj` discharges both conjuncts for `MyOfNat.ofNat`'s body over P3's
--         type-class fixture — a real `TrExprS` through a real `TrProj` — and
--         `gEsrcShapeProj_noProj_refuted` is the other half.
--     Without the second, the field would be satisfiable only where the translation
--     conjunct is vacuous, which is exactly the failure the `envFO` version of
--     `gRecEsrcShape` was caught in (Γ-W4(e)).
#print axioms LeanToLambdaBox.noProjBinders_ofNatBody
#print axioms LeanToLambdaBox.noProj_ofNatBody_refuted
#print axioms LeanToLambdaBox.trExprSQ_ofNatBody
#print axioms LeanToLambdaBox.gEsrcShapeProj
#print axioms LeanToLambdaBox.gEsrcShapeProj_noProj_refuted
--
-- (f) THE RESIDUAL CUT, NAMED. `NoProjBinders` still excludes `let y := self.1; …`: the
--     `letE` clauses stay `NoProj` because `Erases.letE` records BOTH components of the
--     `.vlet` entry and the body's IH runs at a context mentioning them. Lifting that needs
--     the depth-indexed `.vlet` surgery `ErasesUniform`'s section note prices and rejects.
--     It is not a blocker: a prepared class-method body is a λ telescope over a projection,
--     not a `let` over one. And it cannot be lifted by a re-pin either — equational
--     uniqueness at `.proj` is FALSE, not unproved, so the binder clauses are permanent.
--
-- (g) THE CROWN, UNMOVED. Both capstones keep their eight, the bridge its seven,
--     `rec_exit_refines_erases` its six. A slice that admits a whole new class of source
--     terms and changes no axiom set is the outcome (c) was designed for.
#print axioms LeanToLambdaBox.visitExpr_refines_erases
#print axioms LeanToLambdaBox.rec_exit_refines_erases
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart

-- ============================================================================
-- SLICES proj-P5/P6/P7 — THE PROJECTION STEP, END TO END
-- ============================================================================
--
-- The three slices the P0/P1/P4 audit section recorded as NOT independent, landed
-- together because they never were: `SEvalDataι.proj` is one new constructor and three
-- new arms, and two of those arms are the subject reduction and the simulation.
--
-- (a) THE SOURCE RULE. `reduceProj`: the discriminant evaluates to a saturated spine of
--     the structure's own constructor, and spine position `np + i` is selected and
--     evaluated. THE DESIGN'S `hsel : ∃ h, SEvalDataι …` BUNDLE IS REFUTED — it puts the
--     recursive occurrence under `Exists` and the arm loses its induction hypothesis.
--     `hlt`/`hsel` are two fields, exactly as `iota` splits `hidx` from `hbranch`.
#print axioms LeanToLambdaBox.SEvalDataι
--
-- (b) THE INTERFACE MOVED, AND ONE PLANNED LEMMA DIED WITH IT. `ProjConsistent` now takes
--     the UNREDUCED discriminant plus its subject reduction as a function. The P4 form
--     quantified over the reduced redex, which no consumer holds, and bridging the two
--     was the design's `SEvalDataι_proj_congr` — a `TrProj` congruence under a defeq
--     discriminant. It is NOT NEEDED: `ProjDefeqSpec`, and upstream's `TrEnv.proj_defeq`,
--     already take their discriminant up to definitional equality. The congruence the
--     design wanted to prove is the premise the upstream rule wants to be given.
#print axioms LeanToLambdaBox.ProjConsistent
--
-- (c) SUBJECT REDUCTION, AND THE THIRD INDUCTION'S ARM. Three lines and a refutation.
#print axioms LeanToLambdaBox.SEvalDataι_defeq
#print axioms LeanToLambdaBox.SEvalDataι_defeq_of_shape
#print axioms LeanToLambdaBox.SEvalDataι_partial_cases_lam_elim
--
-- (d) THE SIMULATION. `Erases.proj_redex_inv` was never written: `Erases.proj_inv` (P1)
--     IS the two-way split, because `box` and `proj` are the only rules concluding at a
--     projection — no spine arithmetic, no prefix relevance. `ProjRelevant` was not
--     written either: its one surviving clause is `IotaRelevant.ctorValue` with the
--     eliminator hypothesis widened to a disjunction (one field, one use site; nothing in
--     the tree CONSTRUCTS an `IotaRelevant`, so there are no discharge sites to repair).
--     What the case does need is P0's de-opacification, at exactly the predicted line.
#print axioms LeanToLambdaBox.erases_correct_dataι
#print axioms LeanToLambdaBox.ErasesEnvProjsι
--
-- (e) ADDITIVE AT THE GUARDS. Every `Γ` predating the round takes `projs`' default `⊥`,
--     at which all three new premises are THEOREMS. `ΓFOι` discharges them; it does not
--     assume them.
#print axioms LeanToLambdaBox.projConsistent_of_noProjs
#print axioms LeanToLambdaBox.projFieldsCoherent_of_noProjs
#print axioms LeanToLambdaBox.erasesEnvProjsι_of_noProjs
#print axioms LeanToLambdaBox.ΓFOι_erasesEnvProjs
#print axioms LeanToLambdaBox.ΓFOι_certificates
--
-- (f) THE STEP FIRES, BOTH SIDES, AT ONE FIXTURE. `Γproj`/`acΓ`, linked by
--     `projInd = acIid` (`rfl`). `AC` is one parameter and one field, and the parameter
--     and the field are given DIFFERENT erasures, so selecting `np + i = 1` rather than
--     `0` is observable on both sides. `wcbvEval_proj_fires` is the guard the design flags
--     as genuinely new: `LBOptimize_correct`'s non-block `proj` arm is VACUOUS
--     (`simp [defaultFlags] at hb`), so nothing had ever exercised this rule at the flavour
--     the data development runs. `proj_step_fires` is `erases_correct_dataι`'s conclusion
--     tuple built by hand — every component except the two `TrExprS`, which need a
--     `pats`-carrying `env.WF` and are the documented upstream boundary.
#print axioms LeanToLambdaBox.sEvalDataι_proj_fires
#print axioms LeanToLambdaBox.wcbvEval_proj_fires
#print axioms LeanToLambdaBox.proj_step_fires
#print axioms LeanToLambdaBox.projInd_eq_acIid
#print axioms LeanToLambdaBox.Γproj_erasesEnvProjsι
#print axioms LeanToLambdaBox.Γproj_projs_ne_bot
--
-- (g) ⚠️ A DESIGN CLAIM THAT FAILED: `ProjShape` DOES NOT DISCHARGE THE AGREEMENT.
--     §3.1/§3.2 assert that `ival.ctors = [ctor]` supplies `ProjDefeqSpec`'s missing
--     constructor agreement — "the structure has exactly one constructor, so the `TrProj`
--     witness's `ctorName` and the spine's head are the same name". It cannot.
--     `ProjShape` relates `kenv` to `Γ`; the witness's `ctorName` is bound by the
--     `env.pats` membership, i.e. it is a fact about the `VEnv`, which `ProjShape` never
--     mentions. The informal step silently uses a `kenv`↔`env` alignment — which is what
--     a `TrEnv` is, and what the eventual `of_trEnv` will have in hand.
--
--     So the link is NAMED, as `ProjCtorAgree`, in the `PatsIotaSpec`/`ProjDefeqSpec`
--     idiom: a `Prop` hypothesis, never an axiom, refuted at a `pats`-free `env` and with
--     content at `Γproj` (`c = AC.mk`). It is not a new KIND of trust item — it is the
--     `VEnv`-side half of the same `TrEnv.proj_defeq` statement correction this round
--     already escalates upstream.
--
--     `ProjShape` still reaches the arity fact, but only through a `Γ`-side uniqueness
--     side condition (`hone`), which `Γproj_ctorsUnique` discharges by computation. The
--     registration route (`ProjFieldsCoherent`, slice P0) needs neither.
#print axioms LeanToLambdaBox.ProjCtorAgree
#print axioms LeanToLambdaBox.projCtorAgree_of_noPats
#print axioms LeanToLambdaBox.projConsistent_of_arity
#print axioms LeanToLambdaBox.projConsistent_of_coh
#print axioms LeanToLambdaBox.projConsistent_of_shape
#print axioms LeanToLambdaBox.Γproj_ctorsUnique
--
-- (h) THE CROWN, UNMOVED. Three premises added to the ι simulation and its three
--     capstones, one new file, one new source rule — and not one axiom set in this file
--     changed. The bridge keeps its seven, `rec_exit_refines_erases` its six, and both
--     cold-start capstones their eight.
#print axioms LeanToLambdaBox.visitExpr_refines_erases
#print axioms LeanToLambdaBox.rec_exit_refines_erases
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart

-- ============================================================================
-- SLICE proj-P8 — THE BRIDGE COVERS PROJECTIONS
-- ============================================================================
--
-- The last of the projection round's model-side slices, and the one the P1 report named
-- as the obstruction: `Supported.proj` could not be added independently, because step 1
-- of `visitExpr_refines_erases_core` analyses `hsupp` by a COMPLETE `cases`, and the only
-- thing that can discharge a new arm is motive 10 — whose conclusion was `True`.
--
-- (a) THE FOURTH BUNDLE. Two clauses, one per non-recursive call `visitProj` makes, and
--     between them they pin all three fields of the emitted `ProjectionInfo`. Both are
--     Γ↔environment registration agreements and both are `env`/`Us`-free, so THE
--     PROJECTION BRIDGE ADDS NO TYPING ASSUMPTION — the claim `CasesBridgeHyps` makes for
--     itself, and the one this bundle was shaped to keep. No `ProjInfoAgrees` (visitProj
--     reads no `CasesInfo`), no `inferType` clause (the projection path never η-expands),
--     so nothing here is of `BridgeHyps.orc_run`'s elaborator-correctness class.
#print axioms LeanToLambdaBox.ProjBridgeHyps
#print axioms LeanToLambdaBox.ProjBridgeHyps.withFixvars
#print axioms LeanToLambdaBox.ProjBridgeHyps.of_coh
--
-- (b) AND IT IS A THEOREM WHEREVER THE ROUND DOES NOT REACH. Both clauses are keyed on
--     `Γ.projs S = some _`, uninhabited at the default `⊥`, so every context predating the
--     round satisfies the bundle outright. That is what kept the 33 signatures and 34
--     application sites of the threading commit mechanical: they carry a premise that is
--     free at every Γ they instantiate.
#print axioms LeanToLambdaBox.ProjBridgeHyps.of_bot
--
-- (c) THE MASK ARITHMETIC, AND A LIBRARY GAP. `visitProj` computes its field index
--     POST-argmask (`argmasks[0]![:i].toArray.count .keep`) and the model uses `i`; at a
--     trivial mask the two agree, which is where the all-`keep` restriction inherited from
--     `Erases.ctor` is cashed in on the bridge side. It needed its own
--     `count_keep_replicate`: `ConstructorArgRelevance` derives `BEq` but NOT `LawfulBEq`
--     (shipping code, byte-unchanged this round as every round), so the library's
--     count-of-replicate lemmas do not apply and `decide` does not reduce through
--     `Std.Slice.toArray`. The guard is stated with `2 ≠ 3` beside it so it cannot be
--     misread as the degenerate `count = width`.
#print axioms LeanToLambdaBox.count_keep_replicate
#print axioms LeanToLambdaBox.count_keep_take_replicate
--
-- (d) THE RULE, AND THE INVERSIONS THAT COST NOTHING. Every `Supported` inversion the
--     bridge uses already ended in a catch-all (`const_inv'`, `app_inv''`, `lam_inv`,
--     `letE_inv`, `ctorApp_inv`, `casesApp_inv`, `supported_foldl_app_inv`), so the new
--     constructor was absorbed with no edit at all. The two lemmas that ENUMERATE the
--     constructors — `instantiate1'` and `withFixvars` — gain one line each.
#print axioms LeanToLambdaBox.Supported
#print axioms LeanToLambdaBox.Supported.instantiate1'
#print axioms LeanToLambdaBox.Supported.withFixvars
--
-- (e) MOTIVE 10, WITH CONTENT, AND THE STEP. The motive is in the post-Γ-W1 shape
--     (∀ Γ hΓ after the run hypothesis; `RunConclδ` re-indexed to Γ₀; the ⊑ conjunct
--     outside), and it adds exactly ONE IH site — `ih1`, at the local Γ, never the step-6
--     `Γ₀ rfl` column. The admissibility obligation did NOT change:
--     `eraseM_admissible_ok₃` quantifies its `Q` and already named `visitProj` as a client.
--     The step itself is four moves: `projind_run` (state transparency is the THEOREM
--     `run_getConstInfo_state`, so the `unreachable!` arm is dead), `projreg_run` (state
--     effect is the THEOREM `run_register_inductive_runConcl`, not a clause),
--     `count_keep_take_replicate`, and the discriminant's IH.
#print axioms LeanToLambdaBox.visitExpr_refines_erases_core
#print axioms LeanToLambdaBox.visitExpr_refines_erases
#print axioms LeanToLambdaBox.visitExpr_refines_erases_block
--
-- (f) WHY STEP 1's ARM IS TEN LINES. A projection's discriminant is a SUBTERM of its
--     redex, so its translation is read straight off `TrExprS.proj` — no application
--     generation, no `HasType.app_inv`. The same structural fact that made P5's discharge
--     shorter than ι's makes the bridge arm shorter than the `casesApp` one.
--
-- (g) BOTH POLARITIES, AND THE P1 GUARD FLIPPED. The P1-era exclusion held at EVERY Γ for
--     a reason that has now expired; restated, it is the ordinary registration gate that
--     `natLit` has (`Γ.projs = ⊥` makes the rule unusable). Positive: `Supported.proj` at
--     `Γproj` over a variable and over a saturated constructor spine.
#print axioms LeanToLambdaBox.ΓprojQ_projs
#print axioms LeanToLambdaBox.supported_ofNatBodyQ
--
-- (h) THE PAYOFF, AS A GUARD. Guard (v) runs the bridge end to end on
--     `fun (self : MyOfNat N n0) => self.ofNat` — the prepared class-method body whose
--     `Supported` half was the first conjunct `DeltaHyps.prepared` could not satisfy for
--     the typeclass layer. Constructed: `ΓprojQ`, the `BridgeInv`, the `Supported`
--     derivation, and the source translation `trExprSQ_ofNatBody` — the ONE translation in
--     the tree that goes through a `TrProj`. Hypothetical: the run, the four bundles,
--     `DeltaHyps`/`BlockHyps`, and `envQ.Ordered` (`VEnv.Ordered` has no `addPat` clause at
--     this pin — `ProjPattern.lean`'s own note). Every one of those predates the slice.
#print axioms LeanToLambdaBox.trExprSQ_ofNatBody
--
-- (i) THE CROWN, UNMOVED — AND THIS TIME THE WHOLE FILE IS. The 800-entry prefix this
--     slice inherited is BYTE-IDENTICAL after it: a new premise on 33 signatures, a new
--     `Supported` alternative, a motive that stopped being `True`, and not one axiom set in
--     the audit changed. The bridge keeps its seven, `rec_exit_refines_erases` its six,
--     and both cold-start capstones their eight.
#print axioms LeanToLambdaBox.rec_exit_refines_erases
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart

-- ============================================================================
-- SLICE proj-P9 — THE REGISTRY COMPOSITION, AND `hnoprojs` DIES
-- ============================================================================
--
-- The round's last slice, and the only one whose subject is the cold start rather than
-- the model. P5/P6/P7 gave the ι simulation three projection premises; P8 gave the bridge
-- the fourth bundle; both landed with the cold-start ι capstone stated at a
-- STRUCTURE-FREE Γ, because the registry invariant had no `Γ.projs` column and two of the
-- three premises are environment records that have to come off it. This slice grows the
-- column and deletes the restriction.
--
-- (a) THE INVARIANT'S NEW ROW. Two scoped records, `RegisteredProjsOn` and
--     `RegisteredProjCtorFieldsOn`, keyed on `Γ.projs` where `cases`/`fields` are keyed on
--     `Γ.casesOns`, scoped by the same `BlockRegistered s.gdecls`. NOT consequences of the
--     `casesOns` rows: a structure nothing pattern-matches on has `Γ.casesOns = none`
--     everywhere, so those rows are silent about the very block `visitProj` registers —
--     which is the whole reason `ProjFieldsCoherent` is a twin of `CtorFieldsCoherent`
--     rather than an instance of it (slice P0's finding, cashed in here).
#print axioms LeanToLambdaBox.RegisteredProjsOn
#print axioms LeanToLambdaBox.RegisteredProjCtorFieldsOn
#print axioms LeanToLambdaBox.registeredProjs_of_on
#print axioms LeanToLambdaBox.registeredProjCtorFields_of_on
#print axioms LeanToLambdaBox.RegInvShape
--
-- (b) PRESERVATION, MECHANICALLY. Every registration primitive carries the row for the
--     reason the ctor/`casesOn` rows are carried: a `.constantDecl` cons can neither
--     create nor disturb a block registration (`blockRegistered_cons_constantDecl` reads
--     the key inequality OFF the scoping), and an `.inductiveDecl` cons that is not this
--     block passes through `envLookup_cons_of_ne`. No freshness side condition appears,
--     exactly as at S1e. The cold `register_inductive` gains two Γ-agreement premises,
--     `hnewP`/`hnewPF`, in the one place the file already isolates them.
#print axioms LeanToLambdaBox.RegInvShape.empty
#print axioms LeanToLambdaBox.RegInvShape.addAxiom
#print axioms LeanToLambdaBox.RegInvShape.constExt
#print axioms LeanToLambdaBox.RegInvShape.registerInd
#print axioms LeanToLambdaBox.RegInvShape.register_inductive_run
#print axioms LeanToLambdaBox.RegInvShape.constCons
#print axioms LeanToLambdaBox.RegInvShape.recConst
#print axioms LeanToLambdaBox.RegInvShape.registeredProjs
#print axioms LeanToLambdaBox.RegInvShape.registeredProjCtorFields
--
-- (c) THE BUNDLE GROWS THREE FIELDS AND THE SHAPE INDUCTION NONE. `RegBridgeHyps` gains
--     `regProjs`/`regProjFields` — the `regCases`/`regFields` statements transposed onto
--     `Γ.projs`, cold-branch-guarded like their twins, so `regShapeHyps_regCtors_refuted`'s
--     hit-branch instantiation has nowhere to live — and ONE `satProjs`, not two: both new
--     rows are keyed on the same `Γ.projs` lookup, so one completeness fact collapses both.
--     `RunClosed.regInvShape` threads them; `visitExpr_regInvShape` is unchanged AS A
--     STATEMENT, so every consumer of the shape induction picks the column up for free.
--     That is the coverage-field precedent from S1e repeating exactly.
#print axioms LeanToLambdaBox.RegBridgeHyps
#print axioms LeanToLambdaBox.RunClosed.regInvShape
#print axioms LeanToLambdaBox.visitExpr_regInvShape
#print axioms LeanToLambdaBox.visitMutual_regInvShape
#print axioms LeanToLambdaBox.gRegBridgeHyps
#print axioms LeanToLambdaBox.gVisitExpr_regInvShape
--
-- (d) THE COMPOSITION. At the run's final state the two P0 discharges fire on the walked
--     registry: `ErasesEnvProjs` by `erasesEnvProjs_of_registeredProjs`, and
--     `ProjFieldsCoherent` by `projFieldsCoherent_of_registered` — which needs the
--     CONSTRUCTOR record too, so the ι capstone's projection half consumes three of the
--     five columns jointly, the same way its `CtorFieldsCoherent` half consumes three.
--     `hnoprojs : Γ.projs = ⊥` is DELETED from `shipping_erase_correct_firstorderι_coldstart`.
#print axioms LeanToLambdaBox.erasesEnvProjs_of_registeredProjs
#print axioms LeanToLambdaBox.projFieldsCoherent_of_registered
--
-- (e) WHAT SURVIVES AS A PREMISE, AND WHY IT IS NOT AN ENVIRONMENT RECORD. One:
--     `hproj : ProjConsistent env Us Γ`, sitting where `hiota` sits and for the same
--     reason — it is a statement about `env`, so no amount of registry bookkeeping can
--     produce it. Its discharge is `projConsistent_of_coh` on the `ProjFieldsCoherent`
--     the capstone now DERIVES, leaving the two upstream-gated items the round has named
--     since P4/P5: `ProjDefeqSpec` (upstream's `TrEnv.proj_defeq`, a real statement with a
--     deferred proof — commission item A2) and `ProjCtorAgree` (the `env.pats`↔`Γ.ctors`
--     agreement `ProjShape` provably CANNOT supply). Both are `Prop` hypotheses; neither
--     is an axiom, and neither became one here.
#print axioms LeanToLambdaBox.ProjConsistent
#print axioms LeanToLambdaBox.ProjCtorAgree
#print axioms LeanToLambdaBox.projConsistent_of_coh
#print axioms LeanToLambdaBox.projConsistent_of_noProjs
--
-- (f) BOTH POLARITIES AT THE CAPSTONE. Negative: at `ΓprojQ` the deleted premise is
--     REFUTED, not merely unused — the `ΓFOrec_norec_refuted` pattern transposed, and what
--     makes the widening real rather than a re-phrasing. Positive: `ProjFieldsCoherent`
--     holds there NON-DEGENERATELY (`MyOfNat.mk`'s arity 3 = 2 params + 1 field, so a proof
--     confusing `paramCount` with `fieldIdx` would not close), and it is the Γ-side input
--     the `ProjConsistent` discharge runs on. Two premises stop being free at that Γ, which
--     is why the guard is worth running there: `ProjBridgeHyps` can no longer be
--     `of_bot`-instantiated, and `satProjs`'s gate is inhabited (`ΓprojQ_projs`) — the
--     S1d/S1e "satisfiable only vacuously" failure mode, checked for the new column.
#print axioms LeanToLambdaBox.ΓprojQ_noprojs_refuted
#print axioms LeanToLambdaBox.ΓprojQ_projFieldsCoherent
#print axioms LeanToLambdaBox.ΓprojQ_cc
--
-- (g) THE CROWN, UNMOVED — AND THE WHOLE FILE AGAIN. As at P8, the entire inherited prefix
--     is byte-identical after this slice: a structure field added to the registry
--     invariant, three fields added to its bundle, a scope restriction deleted from a
--     capstone, and not one axiom set in the audit changed. The capstones keep their eight,
--     the bridge its seven.
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart
--
-- ============================================================================
-- THE PROJECTION ROUND, CLOSED — WHAT TEN SLICES BOUGHT
-- ============================================================================
--
-- P0 → P9, measured in this file: the round's six audit landings added 135 entries
-- (+12 at P3, +23 at P0/P1/P4, +22 at P2, +28 at P5/P6/P7, +18 at P8, +32 here), and at
-- every one of them the inherited prefix came back byte-identical.
--
-- What the round bought, in one line each:
--
--   P0  `Γ` grew a projection column; `ProjFieldsCoherent` and the two registration
--       records were stated and discharged at a real fixture.
--   P1  `Erases.proj` — the target rule, and eleven inversion arms that were free.
--   P2  `NoProjBinders` — the typeclass layer stopped being excluded by `esrc_shape`.
--   P3  the λ□ side: `WcbvEval.proj` and its metatheory.
--   P4  `ProjDefeqSpec` — the projection-reduction interface, and the hypothesis upstream
--       is missing.
--   P5/P6/P7  the source rule, its subject reduction, and its simulation — plus the
--       finding that `ProjShape` cannot supply the constructor agreement, hence
--       `ProjCtorAgree`.
--   P8  the bridge: the fourth bundle, motive 10 with content, and `Supported.proj`.
--   P9  the registry composition — and `hnoprojs` dies.
--
-- SO: the whole typeclass-dispatch layer — `Expr.proj` in the source, `.proj` in the
-- target, and the structure registration that links them — is inside the cold-start ι
-- capstone's statement, MODULO exactly two named `Prop` hypotheses, both upstream's and
-- both already on the commission: `TrEnv.proj_defeq` (A2, deferred) reaching us as
-- `ProjDefeqSpec`, and `ProjCtorAgree`, the `env`-side half of the same statement
-- correction. No axiom of ours, no `sorry` of ours, and not a byte of the shipping eraser.

-- ============================================================================
-- SLICE Γ-U — THE UNIVERSE BLOCKER, COSTED AND NOT TAKEN
-- ============================================================================
--
-- The projection round removed §H's first leverage item and made `DeltaHyps.prepared`
-- satisfiable for the class-method BODIES. It did not make `DeltaHyps` inhabitable for
-- the class-method DECLARATIONS: every one of them is universe-polymorphic
-- (`OfNat.ofNat.{u}`, `HAdd.hAdd.{u,v,w}`, `Add.add.{u}`, …) while `decl_run` pins
-- `ci.levelParams = Us` and the capstones run at `Us = []`. This slice was commissioned
-- to relax that pin. It lands NO relaxation — two of its five findings say the relaxation
-- is not the cheap half of a bigger job but the WRONG half — and it lands instead the two
-- facts that make the cost measurable, plus the docstring corrections they force.
--
-- Everything below is analysis carried in `DeltaHyps`' module docstring (the five
-- findings), `SubjectReductionFull`'s `SEnvConsistent` docstring (the provenance
-- correction), and `ColdStart`'s `hUs`/`hcon` ledger rows. Two declarations are new.
--
-- (a) THE MODEL'S δ STEP IS UNIVERSE-BLIND — and this is the finding that decided the
--     slice. Every δ rule in the development binds the call site's levels `us` and then
--     DISCARDS them, unfolding `.const n us` to the UNINSTANTIATED body; the kernel
--     unfolds to `body.instantiateLevelParams ci.levelParams us`. The two agree exactly
--     when the instantiation is the identity, i.e. under the pin this slice was asked to
--     remove. The theorem states "discarded" as a theorem: ONE body evaluation serves
--     EVERY level instantiation of the same constant. `sorryAx`-free, and the cheapest
--     entry in this file.
#print axioms LeanToLambdaBox.SEvalDataι.delta_level_blind
--
-- (b) `SEnvConsistent` COLLAPSES A CONSTANT'S INSTANTIATIONS — the same fact one layer
--     up, and the one that was NOT written down anywhere. The premise quantifies `us` and
--     its conclusion never mentions it, so it forces any two level instantiations of a
--     fragment constant definitionally equal. A well-formed `VEnv` does not supply that:
--     `VEnv.IsDefEq.extra` instantiates BOTH sides of a defining equation, so what a
--     `VEnv` gives is `.const n us ≡ ⟦body⟧.instL us`, never two `instL`s to each other.
--     `SEnvConsistent`'s docstring claimed the un-instantiated form; that claim is
--     corrected in place, and this is its refutation.
--
--     AXIOM ACCOUNTING: it inherits `sorryAx` and inherits it from ONE place —
--     `TrExprS.uniq`, whose set is byte-identical and which `erases_correct_data` and its
--     siblings have consumed since long before this slice. Nothing new enters the
--     development's frontier; the guard is a consumer of an item already paid for.
#print axioms Lean4Lean.TrExprS.uniq
#print axioms LeanToLambdaBox.SEnvConsistent.levels_collapse
--
-- (c) WHY THE RELAXATION IS THE WRONG HALF. Three further findings, none of them
--     axiom-visible, all of them in `DeltaHyps`' Γ-U section: `prepared` and `esrc_shape`
--     pin the same monomorphism independently of `decl_run`, so relaxing one clause is a
--     no-op; `Us` is a PARAMETER of `visitExpr_refines_erases_core` rather than a motive
--     binder, and the dependency's sub-run is fed to motive 1's own IH, so there is no
--     composition point outside the induction at which an `instL` could be inserted (the
--     Γ-W1 pattern, at Γ-W1 scale — 343 occurrences of `Us` in a 4452-line file); and
--     `DeltaMem`/`RunConclδ` are `Us`-indexed and chained by `.trans`, so the record
--     cannot stay as it is under a `∀ Us` motive. On top of which `TrExprS.instL` lands
--     in `TrExpr`, not `TrExprS`, while `Erases.box`/`lam`/`letE` record STRICT witnesses
--     — so `Erases.instL`, the lemma the whole plan rests on, is the wall and not a
--     corollary. The ι-era `TrExprS.instL_weak` escapes this only by transporting a
--     closed rhs at `Δ = []`; inside an induction over contexts there is no such escape.
--
-- (d) THE FAILURE MODE, WHICH IS THE POINT. Relaxing `decl_run` and `block_lparams`
--     alone would make `DeltaHyps` inhabitable at a polymorphic dependency and leave the
--     capstones with `hcon : SEnvConsistent` false at exactly those constants. Both are
--     vacuity, so no theorem would become unsound — but one is a named, documented scope
--     restriction and the other is an unnamed premise, and trading the first for the
--     second is a regression in legibility of precisely the kind this ledger exists to
--     prevent. That is why the slice stops here.
--
-- (e) THE CROWN, UNMOVED — AND THE WHOLE FILE AGAIN. No signature changed, no premise
--     moved, no fixture was touched; the slice is two theorems and four docstrings. The
--     capstones keep their eight and the bridge its seven, and the entire inherited
--     850-entry prefix comes back byte-identical.
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart

-- ============================================================================
-- SLICE Γ-W5 — MUTUAL BLOCKS: THE LAST SINGLE-DECLARATION RESTRICTION, LIFTED
-- ============================================================================
--
-- Γ-W3.6b made the bridge WALK `visitMutual`'s recursive exit and Γ-W4 stopped the
-- capstones excluding recursion, but both stood on one clause of
-- `DeltaHyps.decl_run`: `ci.all = [m] ∧ remove_unsafe_rec m = n`. Self-recursion only.
-- Every genuine mutual block — in the subject or anywhere in its dependency cone — made
-- the bundle UNINHABITED, the same failure mode Γ-W2 found one level in when the field
-- still read `ci.all = [n]`.
--
-- The relaxed field states the three facts the walk actually consumes:
--
--     (∀ m ∈ ci.all, known (remove_unsafe_rec m)) ∧
--     (ci.all.map remove_unsafe_rec).Nodup ∧
--     n ∈ ci.all.map remove_unsafe_rec
--
-- and they are a RELAXATION, not a trade: the old pair implies them given the field's
-- own `known n` premise. `gDeclRunMutual_of_single` is that implication; the other two
-- guards are the halves that make it worth having. Twenty entries, all clean.
--
-- (a) THE FIELD. The old conjunct is FALSE at a two-member block, and the new one is
--     inhabited there — including the run's own `single_decl` test coming back `false`,
--     which is what sends such a block down the branch step 6 now walks. `gMutualNames`
--     is the measured fetch shape (`[f._unsafe_rec, g._unsafe_rec]`), so this is the
--     Γ-W0 measurement at arity two.
#print axioms LeanToLambdaBox.gDeclRunMutual_of_single
#print axioms LeanToLambdaBox.gDeclRunSingle_mutual_refuted
#print axioms LeanToLambdaBox.gDeclRunMutual
#print axioms LeanToLambdaBox.gMutualNames_stripped
#print axioms LeanToLambdaBox.gRecExitRegistersBoth
--
-- (b) THE MUTUAL TWIN OF THE `ΓfixRec` FIXTURE, and the reason it had to be built rather
--     than reused. A one-definition block observes NO ordering convention: `defs[0]` is
--     the only def, `fixSubst` has one entry and its reversal is invisible, `closeFix`'s
--     last-sibling-innermost rule has nothing to be last of, and `hreg` has one row. At
--     arity two all four become checkable at once, and `fixMutDefs_unfold_f`/`_g` are
--     where they meet: `f`'s body unfolds to a call of `.fix fixMutDefs 1` and `g`'s to
--     `.fix fixMutDefs 0`, both by `rfl`. Get either convention off by one and those two
--     stop being `rfl`. The block is `def f (a : Prop) := g a` / `def g (a : Prop) := f a`
--     — genuinely mutual, each sibling calling the OTHER, which is the cross-reference
--     `ΓfixRec`'s self-loop cannot exhibit.
#print axioms LeanToLambdaBox.ΓfixMut_recBodies_f
#print axioms LeanToLambdaBox.ΓfixMut_recBodies_g
#print axioms LeanToLambdaBox.ΓfixMut_recBodies
#print axioms LeanToLambdaBox.fixMutDefs_shift
#print axioms LeanToLambdaBox.fixMutDefs_subst
#print axioms LeanToLambdaBox.fixMutDefs_toBvar
#print axioms LeanToLambdaBox.fixMutDefs_unfold_f
#print axioms LeanToLambdaBox.fixMutDefs_unfold_g
#print axioms LeanToLambdaBox.erases_const_fixMut_f
#print axioms LeanToLambdaBox.erases_const_fixMut_g
#print axioms LeanToLambdaBox.erases_fixMut_f
#print axioms LeanToLambdaBox.erases_fixMut_g
--
-- (c) THE WALK, AT THE MUTUAL BLOCK. `rec_exit_refines_erases` and `RecBlockAgreement`
--     were arity-general from the start — that is the whole reason this slice is small —
--     so what had to be shown is that their fragment-side gates are inhabited at two
--     names rather than one. One limitation only became visible here:
--     `bridgeInv_cold_known` is stated at `known = (fun m => m = n)` and cannot express a
--     two-name fragment. It is a specialisation of `bridgeInv_cold_any`, because NO field
--     of `BridgeInv` mentions the fragment at all — the general form is the one a mutual
--     fragment needs, and the old statement is unchanged.
#print axioms LeanToLambdaBox.bridgeInv_cold_any
#print axioms LeanToLambdaBox.gRecBlockRegisteredMutual
#print axioms LeanToLambdaBox.gRecAgreementMutual
--
-- (d) THE CAPSTONE SIDE, AS FAR AS IT IS CONSTRUCTIBLE — and where it stops, which is the
--     finding. `hcov : RecCovered` is the premise that replaced `hnorec` at Γ-W4 and it is
--     `env`-free, so it can be COMPUTED at a two-member registration: `gMutCoveredFO`
--     checks both rows at their OWN indices (`f ↦ (fixMutDefs, 0)`, `g ↦ (fixMutDefs, 1)`
--     — swap them and `recConstState_envLookup`'s membership premise fails), over an
--     environment holding THREE distinct keys rather than two (`gMutKeysFO`).
--     `gMutScope` is the fragment-scope half at a two-name `known`.
--
--     What is NOT constructed is the end-to-end capstone, and the obstruction is
--     `hcon : SEnvConsistent`. `envRec_senvConsistent` discharges it by η, because a
--     self-loop's body IS its own constant's η-expansion. A mutual block's is the OTHER
--     member's, so the premise forces `.const f [] ≡ .const g []` — a defeq BETWEEN THE
--     SIBLINGS, stated as a theorem here rather than asserted. It is the sibling-side twin
--     of Γ-U's `levels_collapse`, proved the same way and carrying `sorryAx` from the same
--     single place (`TrExprS.uniq`, which the whole simulation layer has consumed since
--     long before either slice). An `envMut` discharging `hcon` therefore has to declare
--     one member as a kernel definition of the other, degenerating the source side of the
--     fixture; recorded rather than built. It does NOT block the slice: `hcon` is a
--     capstone premise, not a bundle field, so mutual blocks are in scope for the bridge
--     and for `DeltaHyps` either way.
#print axioms LeanToLambdaBox.ΓFOmut_norec_refuted
#print axioms LeanToLambdaBox.gMutKeysFO
#print axioms LeanToLambdaBox.gMutCoveredFO
#print axioms LeanToLambdaBox.gMutScope
#print axioms LeanToLambdaBox.SEnvConsistent.siblings_collapse
--
-- (d') WHAT THE SLICE DID NOT COST. The multi-declaration arm of step 6 is TEN LINES, and
--     the reason is the shipping eraser's own control flow: at `ci.all.length ≠ 1` the
--     `single_decl` guard skips the whole `@[inline]`/`value?`/`isExtern` prefix, and
--     `nonrecursive` — being `single_decl && …` — is `false` with it, so the run goes
--     straight to the block exit. No inline prefix, no second `getEnv`, no `logInfo`
--     world steps, no axiom exits: the mutual path is SHORTER than the self-recursive
--     one. The single-declaration arm got shorter too, losing the three `have`s that
--     built `hkn'`/`hnd`/`hnmem` out of `ci.all = [mn]`.
--
-- (e) WHAT IT DID NOT BUY, MEASURED. `hcon : SEnvConsistent` and `hUs : Us = []` are
--     untouched, so the §H benchmarks are no closer: their blocker is universe
--     polymorphism (Γ-U), not arity. And the measurement is stronger than that. Reading
--     the arity of every `tFix` block in the five erased programs
--     (`VerifyBench/ast/*.ast`): Arith 4 blocks, Sieve 10, BinaryTrees 10, Quicksort 11,
--     Fannkuch 15, and the defs-per-block histogram is `{1: n}` in EVERY case — not one
--     mutual block among the fifty. So this slice moves ZERO programs into the fragment,
--     which is the Γ-U finding in reverse (a restriction removed rather than costed, with
--     the same null effect on coverage) and is recorded here rather than left to be
--     inferred. It is worth having regardless, for a reason the table cannot show: the
--     restriction was on the whole DEPENDENCY CONE, so one mutual pair anywhere below a
--     program excluded it outright, and nothing was checking. What the slice really
--     removes is a restriction that was invisible in the ledgers precisely because it sat
--     inside a five-conjunct field — the same reason δ-D8e split `nonrecursive` out
--     before trading it.
--
-- (f) THE CROWN, UNMOVED — AND THE WHOLE FILE AGAIN. Twenty-five new declarations plus
--     five crown re-prints (856 → 886), and twenty-four of the twenty-five measure
--     `[propext, Classical.choice, Quot.sound]` or a subset — two of them only `propext`.
--     The twenty-fifth is `SEnvConsistent.siblings_collapse`, which carries `sorryAx` from
--     exactly one place, `TrExprS.uniq`, byte-identically to its Γ-U twin
--     `levels_collapse`: a consumer of an item paid for long ago, not a new frontier.
--     The capstones keep their eight, `visitExpr_refines_erases` its seven and
--     `rec_exit_refines_erases` its six; and the entire inherited 856-entry prefix comes
--     back byte-identical. One
--     signature was generalised (`bridgeInv_cold_any` beside `bridgeInv_cold_known`) and
--     one field relaxed; no axiom, `sorry` or `native_decide` added, and not a byte of
--     the shipping eraser touched.
#print axioms LeanToLambdaBox.visitExpr_refines_erases
#print axioms LeanToLambdaBox.rec_exit_refines_erases
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart

-- ============================================================================
-- SLICE Γ-U1 — THE STRICT HALF: WEAKENING ALONG A PREFIX EXTENSION
-- ============================================================================
--
-- Γ-U stopped at analysis and left a four-slice plan of record. This is its first
-- slice, and the one the analysis singled out as provable where the plan's own
-- transport is not: `TrExprS` (and `Erases`) weakened along a PREFIX EXTENSION
-- `Us <+: Us'` of the level scope, with STRICT conclusions.
--
-- THE ASYMMETRY IS THE WHOLE POINT. `TrExprS.instL` — level SUBSTITUTION — lands in
-- `TrExpr`: it re-derives sort and const levels only up to `≈`, and `Erases.box`/`lam`/
-- `letE` record strict `TrExprS` witnesses, so it is the wall (Γ-U3). A prefix EXTENSION
-- substitutes nothing. `VLevel.ofLevel` resolves a parameter by `List.idxOf`, which
-- returns the FIRST occurrence, and a first occurrence inside the prefix does not move
-- when the list grows on the right (`List.findIdx_append`, positive branch). The very
-- same `VLevel` comes back, the derivation transports on the nose, and the conclusion is
-- a `TrExprS`.
--
-- The slice is a lemma kit in ONE NEW FILE, `ErasesLevels.lean`. It relaxes no bundle
-- field, edits no signature, and has no consumer yet — Γ-U2 is what consumes it, and the
-- Γ-U analysis records why Γ-U2 must not ship alone. Everything below is `sorryAx`-free.
--
-- (a) INDEX STABILITY — the prefix-specific half. `ofLevel` succeeds at `Us'` wherever it
--     succeeded at `Us`, WITH THE SAME `VLevel`. The `<` premise of the `param` arm is
--     `ofLevel`'s own membership test, which is why the append lemma is stated with it
--     rather than with `n ∈ l`.
#print axioms Lean4Lean.List.idxOf_append_of_lt
#print axioms Lean4Lean.VLevel.ofLevel_prefix
#print axioms Lean4Lean.VLevel.mapM_ofLevel_prefix
--
-- (b) UNIVERSE-COUNT MONOTONICITY — the half with nothing to do with prefixes, and the
--     one that was not in the plan at all. `TrExprS` carries `env.HasType Us.length …`
--     and `env.IsType Us.length …` side premises and a `TrProj env Us.length …` arm, so
--     the transport needs the typing judgement to survive a LONGER scope. It does:
--     `IsDefEq` mentions its `uvars` argument at exactly three constructors — `sortDF`,
--     `constDF`, `extra` — and in each only as `VLevel.WF uvars`, which is a conjunction
--     of `i < n` conditions on `param` leaves. Every other rule is `uvars`-blind, so the
--     induction is structural and premise-free: no `env.WF`, no `Ordered`, no `OnCtx`.
#print axioms Lean4Lean.VLevel.WF.uvars_mono
#print axioms Lean4Lean.VEnv.IsDefEq.uvars_mono
#print axioms Lean4Lean.VEnv.HasType.uvars_mono
#print axioms Lean4Lean.VEnv.IsType.uvars_mono
#print axioms Lean4Lean.VEnv.IsDefEqU.uvars_mono
#print axioms Lean4Lean.TrProj.uvars_mono
--
-- (c) THE BOX ARM, RESOLVED HERE AND NOT AT Γ-U3 — the timeboxed risk, which did not
--     materialise. The commission flagged `Erases.box`'s `Erasable env Us.length Δ.toCtx
--     ve` as the place a `VExpr`-side wall might live, and asked for the gap to be stated
--     precisely if it appeared. There is no gap. Unfolded, `Erasable` is a `HasType`
--     together with a `HasType`-or-`IsArityUpTo` disjunct, and all three are `IsDefEq` at
--     `U`; `IsArity` itself never mentions `U`. So `Erasable.uvars_mono` is a corollary
--     of (b) with NO environment-side lift and NO context condition — the answer to
--     "does `Erasable` weaken along more levels?" is yes, unconditionally.
#print axioms LeanToLambdaBox.IsArityUpTo.uvars_mono
#print axioms LeanToLambdaBox.Erasable.uvars_mono
--
-- (d) THE TWO CONCLUSIONS. `TrExprS.prefix_weaken` is the lemma the slice was
--     commissioned for, and it is STRICT — `TrExprS` in, `TrExprS` out. `TrExpr` follows
--     for free (its residual `IsDefEqU` travels by (b)), and is stated for the Γ-U2
--     consumer, which meets `TrExpr` wherever an upstream `instL` has already fired.
--
--     THE `VLCtx` SIDE NEVER ENTERS. `Us` and `Δ` are orthogonal parameters of `TrExprS`;
--     `Δ.toCtx` does not mention `Us`, and the `bvar`/`fvar` arms are pure `VLCtx.find?`
--     lookups. So the family carries no `VLCtx.WF`, no closedness and no freshness
--     premise — which is what distinguishes it from every other transport in the
--     development (`weakBV`, `weakFV`, `abstract`, `instL_weak` all need one).
#print axioms Lean4Lean.TrExprS.prefix_weaken
#print axioms Lean4Lean.TrExpr.prefix_weaken
--
-- (e) `Erases` ITSELF, confirming the Γ-U analysis's finding (a) by construction. The
--     relation mentions `Us` at exactly three constructors and the target `t` never, so
--     the induction is fifteen structural arms plus the three transports above. Same
--     source, same target, same `VExpr` witnesses, no side conditions.
--
--     This is NOT `Erases.instL`. That one is still the wall, and still Γ-U3.
#print axioms LeanToLambdaBox.Erases.prefix_weaken
--
-- (f) THE GUARDS, POSITIVE — a real scope extension through the real lemma, at every
--     layer. `[u]` extended to `[u, v]`: the parameter resolves to `VLevel.param 0` on
--     BOTH sides (index stability, decided); the `TrExprS` fixture is a sort, which is
--     the constructor that pins the `VLevel` on the nose; the `Erases` fixture is a `lam`
--     whose binder type is that sort, which is one of the three arms that carry a strict
--     `TrExprS`. Both fixtures are built at an ARBITRARY `env`/`Γ`/`Δ`, so what they
--     check is the level scope and nothing else.
#print axioms LeanToLambdaBox.guard_uv_prefix
#print axioms LeanToLambdaBox.ofLevel_prefix_index_stable
#print axioms LeanToLambdaBox.trExprS_sort_prefix_weaken_guard
#print axioms LeanToLambdaBox.erases_lam_prefix_weaken_guard
--
-- (g) THE GUARDS, NEGATIVE — the hypothesis is not slack. The commission asked for the
--     non-prefix case as a comment "or a refutation if cheap". It is cheap, so it is a
--     refutation. A PERMUTATION preserves the parameter set AND the scope length — it
--     satisfies everything (b) needs — and still breaks the lemma, because `idxOf`
--     returns a position and not a name: `u` sits at `0` in `[u, v]` and at `1` in
--     `[v, u]`. Two refutations, at the level layer and at the `TrExprS` layer, the
--     second at EVERY environment. They are the machine-checked reason
--     `VLevel.ofLevel_prefix` says `<+:` and not "same names".
#print axioms LeanToLambdaBox.ofLevel_perm_index_shifts
#print axioms LeanToLambdaBox.not_ofLevel_weaken_of_perm
#print axioms LeanToLambdaBox.not_trExprS_weaken_of_perm
--
-- (h) THE CROWN, UNMOVED — AND THE WHOLE FILE AGAIN. The slice adds one file and one
--     import line; it edits no existing declaration, no signature and no fixture. The
--     entire inherited 886-entry prefix comes back BYTE-IDENTICAL, verified by diffing a
--     full run against a run of the same file at `e0e2b16` with the new module stashed.
--     The capstones keep their eight and the bridge its seven.
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder_coldstart
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorderι_coldstart
