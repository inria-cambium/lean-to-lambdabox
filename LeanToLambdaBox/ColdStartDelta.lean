import LeanToLambdaBox.ColdStartRun
import LeanToLambdaBox.EnvErasureRec
import LeanToLambdaBox.ErasesUniform

/-!
# The δ half of the cold-start registry invariant (slice S3)

`ColdStartShape`/`ColdStartInduction` carry the **shape** half of the registration record
through a whole run: what is registered agrees with `Γ`, the keys stay distinct, and every
stored body is fix-free and de-Bruijn closed. What they cannot carry is the **δ** half —
that the stored body *erases* the source body `Esrc` records. The reason is structural and
worth stating once, because it is what fixes this slice's architecture:

* the shape half travels as a state predicate `Q : ErasureState → Prop`
  (`RunClosed`, `visitExpr_shape`), and a state predicate has no room to mention the
  `visitExpr` run whose *output* is being stored;
* widening the predicate is not an option either: inside
  `Erasure.visitExpr.mutual_fixpoint_induct` the step goal for `visitMutual` sees the
  fixpoint's **abstract** erasure argument, so a bridge fact about the real
  `Erasure.visitExpr` is unusable there;
* and the bridge induction cannot host the content either. Slice D4a did give its motive
  6 content, but only what the *state* records (`RunConclδ`, generator monotonicity, "`n`
  is now registered"); the δ witness needs the abstract erasure argument to deliver
  *output shapes*, which would mean merging the two 18-motive inductions.

So the δ content is composed **outside** every induction, about the real functions, from
`ColdStartRun.run_visitMutual_decomp` — which hands the inner `Erasure.visitExpr` run
back — plus the bridge (`erases_nonrec_const_body`) and the output-shape corollary
(`visitExpr_noFix_closed`). That is `erases_nonrec_const_registered` below: **after a
`visitMutual n` call that took the non-recursive exit, the body the run recorded in
`gdecls` really is an erasure of the body it erased.**

## What is discharged and what is not

| obligation | status |
|---|---|
| the stored entry is *there*, under `Γ.constants n` (non-recursive exit) | **proved** (`erases_nonrec_const_registered`) |
| the stored entry erases the prepared source body, at `Δ = []` | **proved** (same) |
| the stored entry is fix-free and closed | **proved** (`visitExpr_noFix_closed`) |
| the stored entry is *there* (recursive exit) | **proved** (`recConstState_envLookup`) |
| the recursive entry erases its source body | **proved from the run** (`erases_rec_block_of_run`, slice δ-D8), modulo the `Γ`↔run registration agreement — see the recursion section |
| context-uniformity (`∀ Δ`) of a constant body's erasure | **proved** (`ErasesUniform.erases_uniform_closed`), modulo the one commissioned `ErasableStrengthen` |
| `Esrc`-domain ↔ walk agreement | **named premise** — `Esrc` and `Γ` are parameters |

The `∀ Δ` line used to read "no *weakening* over a closed subject, and adding one is a
lean4lean-side `TrExprS`-weakening obligation". That was wrong on both counts: the
weakening exists upstream and the erasure-side transports are now proved here
(`ErasesStrengthen.erases_weakFV`/`erases_weak_any`). What is genuinely missing is
`Erasable`/`HasType` *strengthening*, which is `ErasesUniform.ErasableStrengthen`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

/-! ## `envLookup` from membership, and lookup stability under growth -/

/-- With distinct keys, membership *is* lookup: no earlier entry can shadow. -/
theorem envLookup_of_mem_of_keys : ∀ {E : GlobalDeclarations} {kn : Kername}
    {d : GlobalDecl}, (kn, d) ∈ E → KeysDistinct E → LBTerm.envLookup E kn = some d
  | [], _, _, hmem, _ => absurd hmem (by simp)
  | (k, d') :: rest, kn, d, hmem, hkeys => by
    rcases List.mem_cons.mp hmem with heq | hmem'
    · cases heq
      exact envLookup_cons_self _ _ _
    · have hne : Kername.beq k kn = false := by
        have := (List.pairwise_cons.mp hkeys).1 (kn, d) hmem'
        simpa using this
      simp only [LBTerm.envLookup, hne, Bool.false_eq_true, if_false]
      exact envLookup_of_mem_of_keys hmem' (KeysDistinct.of_cons hkeys)

/-- **Lookup stability along the walk.** An entry established at an intermediate state
survives to the final one, provided the final `gdecls` still has distinct keys. This is the
lemma that makes a registration record proved *at the moment of registration* usable *at
the end of the run*.

`hkeys` is a premise here and stays one: slice S1e removed `KeysDistinct` from
`RegInvShape`, having proved that no state predicate carried along the shape induction can
maintain it (`ColdStartInduction.runClosed_keysDistinct_refuted`). What the invariant does
give a caller is `RegInvShape.fresh_of_unregistered`: freshness of a not-yet-registered
name against the constant keys, which is the step from which a `KeysDistinct` is *built*
when the caller knows the walk does not re-register. -/
theorem envLookup_mono_of_keys {E E' : GlobalDeclarations} {kn : Kername} {d : GlobalDecl}
    (hgrow : ∃ pre, E' = pre ++ E) (hkeys : KeysDistinct E')
    (h : LBTerm.envLookup E kn = some d) : LBTerm.envLookup E' kn = some d := by
  obtain ⟨pre, rfl⟩ := hgrow
  obtain ⟨k, hmem, hbeq⟩ := envLookup_mem h
  obtain rfl := Kername.eq_of_beq hbeq
  refine envLookup_append_of_fresh h (fun p hp => ?_)
  exact (List.pairwise_append.mp hkeys).2.2 p hp (k, d) hmem

/-- The `StateLe`-shaped form. -/
theorem envLookup_mono_stateLe {s s' : ErasureState} {kn : Kername} {d : GlobalDecl}
    (hle : StateLe s s') (hkeys : KeysDistinct s'.gdecls)
    (h : LBTerm.envLookup s.gdecls kn = some d) :
    LBTerm.envLookup s'.gdecls kn = some d :=
  envLookup_mono_of_keys hle.gdecls hkeys h

/-! ## The non-recursive exit's δ content

The one place the whole chain meets: a real `visitMutual` call's inner run, the bridge,
and the output-shape induction. -/

/-- **The recorded body erases (non-recursive exit).** `hvis`/`hpost` are what
`ColdStartRun.run_visitMutual_decomp`'s middle disjunct hands back; `hinv`/`hsupp`/`hex`
are the bridge's own inputs at the *dependency*'s reader context (`visitMutual` erases a
constant body at `Δ = []`, under `fixvars := none` and the declaration's own
`levelParams`); `hknames` is the design's `hknames`, which is what identifies the key the
run conses (`Erasure.toKername n`) with the key `Γ` files the constant under.

Nothing here is assumed about the state: the entry's presence is read off the cons the
decomposition reports, and its shape off `visitExpr_noFix_closed`, which has no
hypotheses at all. -/
theorem erases_nonrec_const_registered {env : VEnv} {Us : List Name} {known : Name → Prop}
    {Γ : ErasureCtx} {Esrc : SEnv} {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps env Us known Γ Esrc gw cc rf)
    (henv : env.Ordered) (hknames : ∀ m : Name, Γ.constants m = toKername m)
    {n : Name} {pe : Expr} {t : LBTerm} {sp st s₁ : ErasureState}
    {ctx' : ErasureContext} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {wp wt : Void IO.RealWorld}
    (hvis : Erasure.visitExpr pe sp ctx' cctx ref wp = .ok (t, st) wt)
    (hinv : BridgeInv env Us known Γ (gw wp) ctx' sp [])
    (hsupp : Supported known Γ pe)
    (hex : ∃ ve, TrExprS env Us [] pe ve)
    (hpost : InlineExt (nonrecConstState n t st) s₁) :
    LBTerm.envLookup s₁.gdecls (Γ.constants n) = some (.constantDecl ⟨some t⟩) ∧
      Erases env Us Γ [] pe t ∧ NoFix t ∧ LBClosed t 0 := by
  obtain ⟨hnf, hcl⟩ := visitExpr_noFix_closed hvis
  refine ⟨?_, erases_nonrec_const_body H HD C Hδ henv hvis hinv hsupp hex, hnf, hcl⟩
  rw [hpost.gdecls, hknames n]
  exact envLookup_cons_self _ _ _

/-! ## The recursive exit's registration

The δ *witness* for a recursive block is `EnvErasureRec.erases_fix_of_open`, whose premise
list is a dozen facts about the block (`closeFix` agreement, closedness and fvar-freeness
of the stored node, the `Γ.recBodies` links, the per-sibling open erasures). Producing
those from a run means reading them off the `List.mapM` over `names` that
`run_rec_exit_decomp` steps past.

Slice D6 builds that per-sibling decomposition — `ColdStartRun.run_rec_exit_siblings`, and
its immediate corollary `run_rec_exit_siblings_closed` — so the loop is no longer a wall.
What it delivers, against `erases_fix_of_open`'s premise list:

| premise | after D6 |
|---|---|
| `hoclosed` (each open body is `LBClosed`) | **from the run** (`visitExpr_noFix_closed`, per sibling) |
| `hffv` (the stored block is fvar-free) | **derived**, and gone from `erases_rec_block_of_run`'s signature: a block-local erasure of an fvar-free source has only fixvars free in its target (`EnvErasureRec.erases_target_fvars`), `hfv` says those fixvars are the run's own `ids`, and `closeFix` abstracts exactly the `ids` (`FixUnfold.not_hasFVar_closeFix`). It was never an independent fact about the block — it is a consequence of `hopen` plus `hclose` |
| `hclose` (`defs[j].body` closes `obodies[j]`) | **from the run**, and since δ-D8 in `closeFix` form outright (`run_rec_exit_siblings_close`): `mkDef`'s fold looks each sibling's *name* up in the reader's map where `closeFix` abstracts the `ids`, and `closeFix_eq_block_fold` discharges the difference from the block names being distinct |
| `hfv` (the block map names the block's own ids) | **from the reader** (`blockMap_getElem?_inv`, δ-D8), for `fv` read off the map the run installed |
| the per-sibling `visitExpr` runs feeding `hopen` | **from the run** |
| `hilen`/`hnlen`/lengths | **from the run** |
| `hnd : ids.Nodup` | freshness — `BridgeHyps.fresh_run`'s business, and the loop rule here is `gw`-free by design |
| `hreg` (`Γ.recBodies` names *this* block) | **irreducible at a parameter `Γ`**: `Γ` is fixed before the run, so no run fact can say it names a block the run built. This is the run-keyed agreement that *replaces* `RegisteredClosureRec` (slice δ-D8) |
| `hsrc`/`heclosed`/`henofv`/`hsrcfv` (the source body is a closed, fvar-free λ) | `PrepareHyps`-class facts about the prepared value |
| `hopen`'s `∀ Δf` | **gone** (slice δ-D8). `rec` conditioned it on a fresh `Δf`; the proof instantiates it at `Δf := []` and nowhere else, so `erases_fix_of_open_nil` states it there. That is the shape a *run* can supply |
| `hopen` at the block-local `Γ.withFixvars fv` | **from the bridge** (slice δ-D8): `VisitExprRefines.visitExpr_refines_erases_block`. No motive changes — the bridge theorem is Γ-polymorphic as a statement, and exactly one premise breaks at `Γ.withFixvars fv` (`DeltaHyps.nofixvars`, now conditioned on the fragment) |
| `hlink`, `hnest` | scoped premises; `hlink` is derived from `hreg` plus the block map, `hnest` is unreachable in the intended use (see its docstring) |

So the *demotion* is performed, below: `erases_rec_block_of_run` turns the per-sibling
block-local erasures into the `Erases.fix` derivation at the outer `Γ`, at every context,
and `recEnvConsistent_of_block` turns that into the environment-level record. What
`EnvErasureRec.RegisteredClosureRec` used to assert as a certificate is now a *theorem*
about the run, modulo the `Γ`↔run registration agreement (`hreg`/`hfv`/`hcov`), which is
`BridgeInv.knames`-class rather than `Erases`-class, and `hnest`.

**The one scope restriction this buys, stated honestly.** The block's inner runs are taken
at `known = ⊥`, so `Supported (fun _ => False) (Γ.withFixvars fv) body` forces every
`.const` in a block body to be a sibling, a registered constructor or a registered
`casesOn`. **A mutual block whose bodies call an external constant is out of scope.**
Lifting that needs `DeltaHyps` to carry the *dependency's* context as a second parameter
and motives 1/5/6 to quantify `Γ`, because such a callee is genuinely erased at a third
`Γ` (`fixvars := none`); nothing else in this section needs it.

**What is still not wired to the capstones, and why.** The cold-start capstones' `hnorec`
does *not* trade for these results yet, and the obstruction is upstream of them:
`DeltaHyps.decl_run` demands `name_occurs n v = false` for every fragment name, which
forces `visitMutual`'s `nonrecursive` test `true` — so the bridge's step 6 refutes the
recursive exit rather than walking it (`VisitExprRefines`, case `isFalse hnr`). A cold
start therefore never *takes* the recursive exit inside the fragment, and there is no run
for these theorems to consume there. Wiring them in means giving step 6 a recursive branch
— `RunConclδ`'s `δ` transport across `recConstState` (which is exactly
`erases_rec_block_of_run`'s conclusion, so it composes), the generator bookkeeping for the
block's `mkFreshFVarId`/`getConstInfo` loop, and one further scope restriction, since the
registration is keyed on `remove_unsafe_rec n` and not on `n`.

What *is* discharged from the run, and was before, is the registration half: the block
really is in `gdecls`, under the canonical kername, at the sibling's own index. -/

/-- Each sibling of a recursive block is consed by `Erasure.recConstState`. -/
theorem mem_recConstState_gdecls (defs : List (@FixDef LBTerm)) :
    ∀ (L : List (Name × Nat)) (s : ErasureState) (p : Name × Nat), p ∈ L →
      (toKername p.1, GlobalDecl.constantDecl ⟨some (.fix defs p.2)⟩)
        ∈ (L.foldl (Erasure.recConstStep defs) s).gdecls
  | [], _, _, hp => absurd hp (by simp)
  | q :: rest, s, p, hp => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · obtain ⟨pre, hpre⟩ := recConstFold_gdecls defs rest (Erasure.recConstStep defs s p)
      rw [hpre]
      refine List.mem_append_right _ ?_
      show _ ∈ (nonrecConstState p.1 (.fix defs p.2) s).gdecls
      simp [nonrecConstState]
    · exact mem_recConstState_gdecls defs rest _ p hp'

/-- **The recursive block is registered.** For every `(m, j)` of the block, the final
`gdecls` looks up `Erasure.toKername m` to the stored `.fix defs j` — the `envLookup`
conjunct of `RegisteredClosureRec.erase` and of `RecEnvConsistent.reg`, proved from the
run rather than assumed. Key distinctness — a premise of the caller since slice S1e, see
`envLookup_mono_of_keys` — is what turns membership into lookup. -/
theorem recConstState_envLookup {names : List Name} {defs : List (@FixDef LBTerm)}
    {s : ErasureState} {m : Name} {j : Nat} (hmem : (m, j) ∈ names.zipIdx)
    (hkeys : KeysDistinct (recConstState names defs s).gdecls) :
    LBTerm.envLookup (recConstState names defs s).gdecls (toKername m)
      = some (.constantDecl ⟨some (.fix defs j)⟩) := by
  rw [recConstState_eq] at hkeys ⊢
  exact envLookup_of_mem_of_keys
    (mem_recConstState_gdecls defs names.zipIdx s (m, j) hmem) hkeys

/-! ### The block's δ witness, assembled (slice δ-D8)

This is the demotion the ledger above asks for. `EnvErasureRec.RegisteredClosureRec` is a
monolithic certificate: it *asserts* that the recorded block erases the source body, at
every context. What replaces it is two things that are not certificates —

* the **run**: D6's per-sibling `prepare_erasure`/`visitExpr` runs at the block's own
  reader, plus `mkDef`'s closing equation and the per-sibling output shape;
* one **agreement**, `hreg`/`hfv`: "the `Γ` you supply names *this* block, under the map
  the run installed". That one is irreducible — `Γ` is fixed before the run builds `defs`,
  so no run fact can say it — and it changes epistemic class rather than disappearing:
  from an `Erases` witness to a registration agreement, the same class as
  `BridgeInv.knames`.

Everything between them is now derived: the erasure of each sibling body comes from the
bridge instantiated at `Γ.withFixvars fv`
(`VisitExprRefines.visitExpr_refines_erases_block`), and `erases_fix_of_open_nil` turns the
per-sibling open erasures into the `Erases.fix` derivation at the *outer* `Γ`, at every
context. -/

/-- **The reader `visitMutual` installs while erasing a mutual block** — its
`withReader (fun env => { env with fixvars := fixvarnames.zip ids |> ofList |> some })`,
named so the block's two lookups (`mkDef`'s closing fold and the bridge's fixvar
agreement) can be stated about the same object. -/
def blockReader (fixnames : List Name) (ids : List FVarId) (ctx : ErasureContext) :
    ErasureContext :=
  { ctx with fixvars := some (Std.HashMap.ofList (fixnames.zip ids)) }

@[simp] theorem blockReader_fixvars (fixnames : List Name) (ids : List FVarId)
    (ctx : ErasureContext) :
    (blockReader fixnames ids ctx).fixvars
      = some (Std.HashMap.ofList (fixnames.zip ids)) := rfl
@[simp] theorem blockReader_lctx (fixnames : List Name) (ids : List FVarId)
    (ctx : ErasureContext) : (blockReader fixnames ids ctx).lctx = ctx.lctx := rfl
@[simp] theorem blockReader_lparams (fixnames : List Name) (ids : List FVarId)
    (ctx : ErasureContext) : (blockReader fixnames ids ctx).lparams = ctx.lparams := rfl
@[simp] theorem blockReader_config (fixnames : List Name) (ids : List FVarId)
    (ctx : ErasureContext) : (blockReader fixnames ids ctx).config = ctx.config := rfl

/-- Distinct block names give a `HashMap.ofList`-admissible association list. -/
theorem zip_pairwise_fst : ∀ {nms : List Name} {ids : List FVarId}, nms.Nodup →
    (nms.zip ids).Pairwise (fun a b => (a.1 == b.1) = false)
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: l, b :: m, hnd => by
      rw [List.zip_cons_cons]
      refine List.Pairwise.cons ?_ (zip_pairwise_fst (List.nodup_cons.mp hnd).2)
      intro p hp
      have hmem : p.1 ∈ l := (List.of_mem_zip (a := p.1) (b := p.2) (by simpa using hp)).1
      have : a ≠ p.1 := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hmem)
      simpa using this

/-- **The block map at a sibling's own name** — the lookup `mkDef`'s fold performs. -/
theorem blockMap_getElem! {nms : List Name} {ids : List FVarId}
    (hnd : nms.Nodup) (hlen : nms.length = ids.length)
    {k : Nat} (hk : k < nms.length) :
    (Std.HashMap.ofList (nms.zip ids))[nms[k]]! = ids[k]'(hlen ▸ hk) := by
  refine Std.HashMap.getElem!_ofList_of_mem (k := nms[k]) (by simp) (zip_pairwise_fst hnd) ?_
  have hz : (nms.zip ids)[k]'(by simp [← hlen]; omega) = (nms[k], ids[k]'(hlen ▸ hk)) := by
    simp
  exact hz ▸ List.getElem_mem _

/-- **…and the inverse**: a hit in the block map really is one of the block's own ids, at
the matching index. This is what supplies `erases_rec_block_of_run`'s `hfv` when `fv` is
read off the reader the run installed. -/
theorem blockMap_getElem?_inv {nms : List Name} {ids : List FVarId}
    (hnd : nms.Nodup) (hlen : nms.length = ids.length) {nm : Name} {x : FVarId}
    (h : (Std.HashMap.ofList (nms.zip ids))[nm]? = some x) :
    ∃ k, ∃ hk : k < nms.length, nms[k] = nm ∧ (ids[k]'(hlen ▸ hk)) = x := by
  by_cases hmem : nm ∈ nms
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hmem
    refine ⟨k, hk, rfl, ?_⟩
    have hz : (nms.zip ids)[k]'(by simp [← hlen]; omega) = (nms[k], ids[k]'(hlen ▸ hk)) := by
      simp
    have hget : (Std.HashMap.ofList (nms.zip ids))[nms[k]]? = some (ids[k]'(hlen ▸ hk)) :=
      Std.HashMap.getElem?_ofList_of_mem (by simp) (zip_pairwise_fst hnd)
        (hz ▸ List.getElem_mem _)
    rw [hget] at h
    exact Option.some.inj h
  · exfalso
    rw [Std.HashMap.getElem?_ofList_of_contains_eq_false ?_] at h
    · simp at h
    · rw [List.map_fst_zip (by omega)]
      simpa using hmem

/-- **`mkDef`'s binder fold *is* `closeFix ids 0`.** The shipping loop abstracts the
block's fvars by looking each sibling's name up in the reader's map; `closeFix` abstracts
the `ids` directly. `FixMetatheory` has always said the two agree "modulo the `fixvars`
lookup" — this is that modulo, discharged, and it needs exactly the block names' being
distinct. -/
theorem closeFix_eq_block_fold {nms : List Name} {ids : List FVarId}
    (hnd : nms.Nodup) (hlen : nms.length = ids.length) (t : LBTerm) :
    nms.reverse.zipIdx.foldl
        (fun b p => toBvar ((Std.HashMap.ofList (nms.zip ids))[p.1]!) p.2 b) t
      = closeFix ids 0 t := by
  have hids : ids.reverse
      = nms.reverse.map (fun nm => (Std.HashMap.ofList (nms.zip ids))[nm]!) := by
    rw [List.map_reverse]
    congr 1
    refine List.ext_getElem (by simp [hlen]) (fun k h1 h2 => ?_)
    rw [List.getElem_map]
    exact (blockMap_getElem! hnd hlen (by simpa [hlen] using h1)).symm
  rw [closeFix, closeFixFold_eq_foldl, hids, List.zipIdx_map, List.foldl_map]
  rfl

/-- **D6's decomposition, in `closeFix` form** — `run_rec_exit_siblings` with the reader
pinned to the one `visitMutual` installs and `mkDef`'s fold already inverted. This is the
shape `erases_rec_block_of_run` consumes: per sibling, the `prepare_erasure` and
`visitExpr` runs at the block's own reader, the output's `NoFix`/`LBClosed`, and the
`hclose` equation. -/
theorem run_rec_exit_siblings_close {names : List Name}
    {g : ConstantInfo → ErasureContext → ErasureContext} {val : ConstantInfo → Expr}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hnd : (names.map remove_unsafe_rec).Nodup)
    (hrun : (do
        let ids ← names.mapM (fun _ => mkFreshFVarId)
        withReader (blockReader (names.map remove_unsafe_rec) ids) (do
          let defs ← names.mapM (fun m => do
            let ci ← getConstInfo m
            let t ← withReader (g ci) (do let pe ← prepare_erasure (val ci); visitExpr pe)
            mkDef (remove_unsafe_rec m) (names.map remove_unsafe_rec) t)
          for p in (names.map remove_unsafe_rec).zipIdx do
            modify (fun s => { s with
              constants := s.constants.insert p.1 (toKername p.1),
              gdecls := (toKername p.1, .constantDecl ⟨some (.fix defs p.2)⟩) :: s.gdecls })
          pure ()) : EraseM Unit) s ctx cctx ref w = .ok (u, s₁) w₁) :
    ∃ (ids : List FVarId) (defs : List (@FixDef LBTerm)) (sd : ErasureState),
      ids.length = names.length ∧ defs.length = names.length ∧
      s₁ = recConstState (names.map remove_unsafe_rec) defs sd ∧
      ∀ (j : Nat), j < names.length →
        ∃ (ci : ConstantInfo) (pe : Expr) (t : LBTerm)
          (sa sb sc : ErasureState) (wa wb wc : Void IO.RealWorld) (hd : j < defs.length),
          prepare_erasure (val ci) sa
              (g ci (blockReader (names.map remove_unsafe_rec) ids ctx))
              cctx ref wa = .ok (pe, sb) wb ∧
          visitExpr pe sb
              (g ci (blockReader (names.map remove_unsafe_rec) ids ctx))
              cctx ref wb = .ok (t, sc) wc ∧
          NoFix t ∧ LBClosed t 0 ∧
          (defs[j]'hd).body = closeFix ids 0 t := by
  obtain ⟨ids, defs, sd, hil, hdl, hs, hpkg⟩ := run_rec_exit_siblings hrun
  refine ⟨ids, defs, sd, hil, hdl, hs, fun j hj => ?_⟩
  obtain ⟨d, ci, pe, t, sa, sb, sc, wa, wb, wc, hd, hpr, hvis, -, hbody⟩ := hpkg j hj
  obtain ⟨hnf, hcl⟩ := visitExpr_noFix_closed hvis
  have hdj : j < defs.length := by omega
  obtain rfl : (defs[j]'hdj) = d := by
    rw [List.getElem?_eq_getElem hdj] at hd; exact Option.some.inj hd
  refine ⟨ci, pe, t, sa, sb, sc, wa, wb, wc, hdj, hpr, hvis, hnf, hcl, ?_⟩
  rw [hbody]
  show (List.map remove_unsafe_rec names).reverse.zipIdx.foldl
      (fun b p => toBvar ((Std.HashMap.ofList
        ((List.map remove_unsafe_rec names).zip ids))[p.1]!) p.2 b) t = _
  exact closeFix_eq_block_fold hnd (by simp [hil]) t

/-- **From the block's open erasures to `Erases.fix`.** The `hopen` slot is exactly what
`visitExpr_refines_erases_block` produces for one sibling; everything else is the run's
own output shape (`ColdStartRun.run_rec_exit_siblings{,_closed}`) or the `Γ`-side
agreement. The conclusion is context-uniform, which is what the environment-level records
need.

Fvar-freeness of the stored block is **derived** here rather than assumed: it is not an
independent fact about `defs` but a consequence of the block-local erasures plus the
closing — `erases_target_fvars` says every free variable of an opened body is a fixvar of
`Γ.withFixvars fv`, `hfv` identifies those with the run's own `ids`, and
`not_hasFVar_closeFix` observes that `closeFix ids 0` abstracts precisely the `ids`. -/
theorem erases_rec_block_of_run {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Γ : ErasureCtx} (hnfv : Γ.fixvars = fun _ => none)
    {fv : Name → Option FVarId}
    {fixnames : List Name} {ids : List FVarId} {srcs : List Expr} {obodies : List LBTerm}
    {defs : List (@FixDef LBTerm)}
    (hnlen : fixnames.length = defs.length)
    (hilen : ids.length = defs.length)
    (hslen : srcs.length = defs.length)
    (hblen : obodies.length = defs.length)
    (hnd : ids.Nodup)
    -- the one irreducible `Γ`↔run agreement, in two halves: the registration and the map
    (hreg : ∀ j (h : j < defs.length),
        Γ.recBodies (fixnames[j]'(hnlen ▸ h)) = some (defs, j))
    (hfv : ∀ (nm : Name) (x : FVarId), fv nm = some x →
        ∃ j, ∃ h : j < defs.length,
          (fixnames[j]'(hnlen ▸ h)) = nm ∧ (ids[j]'(hilen ▸ h)) = x)
    -- the block, as the run built it
    (hrarg : ∀ d ∈ defs, d.principalArgIdx = 0)
    (hfclosed : ∀ j : Nat, LBClosed (.fix defs j) 0)
    (hoclosed : ∀ j (h : j < defs.length), LBClosed (obodies[j]'(hblen ▸ h)) 0)
    (hclose : ∀ j (h : j < defs.length),
        (defs[j]'h).body = closeFix ids 0 (obodies[j]'(hblen ▸ h)))
    -- the block's sources: closed, fvar-free λ-telescopes, as a top-level def body is
    (hsrc : ∀ j (h : j < defs.length),
        ∃ n ty b bi, (srcs[j]'(hslen ▸ h)) = .lam n ty b bi)
    (hsclosed : ∀ j (h : j < defs.length), Closed (srcs[j]'(hslen ▸ h)) 0)
    (hsrcfv : ∀ j (h : j < defs.length),
        FVarsIn (fun _ => False) (srcs[j]'(hslen ▸ h)))
    -- the block-local erasures — the Γ'-instantiated bridge's output, one per sibling
    (hopen : ∀ j (h : j < defs.length),
        Erases env Us (Γ.withFixvars fv) [] (srcs[j]'(hslen ▸ h))
          (obodies[j]'(hblen ▸ h)))
    (hnest : ∀ {Δ' : VLCtx} {n' : Name} {ty' b' : Expr} {bi' : BinderInfo}
        {d' : List (@FixDef LBTerm)} {i' : Nat},
        Erases env Us (Γ.withFixvars fv) Δ' (.lam n' ty' b' bi') (.fix d' i') →
        Erases env Us Γ Δ' (.lam n' ty' b' bi') (.fix d' i')) :
    ∀ j (h : j < defs.length) (Δ : VLCtx),
      Erases env Us Γ Δ (srcs[j]'(hslen ▸ h)) (.fix defs j) := by
  intro j h Δ
  -- Fvar-freeness of the stored block, derived. Each def body is `closeFix ids 0` of the
  -- matching opened body (`hclose`); every free variable of that opened body is a fixvar
  -- of the block-local `Γ` (`erases_target_fvars` applied to `hopen`), hence one of the
  -- run's `ids` (`hfv`); and `closeFix ids 0` abstracts exactly those.
  have hffv : ∀ (x : FVarId) (k : Nat), ¬ hasFVar x (.fix defs k) := by
    intro x k hx
    rw [hasFVar_fix, hasFVarDefs_iff] at hx
    obtain ⟨d, hd, hxd⟩ := hx
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hd
    rw [hclose m hm] at hxd
    refine not_hasFVar_closeFix (fun z hz => ?_) 0 x hxd
    obtain ⟨nm, hnm⟩ := erases_target_fvars (hopen m hm) (hsrcfv m hm) hz
    rw [ErasureCtx.withFixvars_fixvars] at hnm
    obtain ⟨i, hi, -, rfl⟩ := hfv nm z hnm
    exact List.getElem_mem _
  obtain ⟨n, ty, b, bi, hsj⟩ := hsrc j h
  rw [hsj]
  refine erases_fix_of_open_nil henv hnfv (nms := fixnames) (ids := ids) (srcs := srcs)
    (obodies := obodies) h hnlen hslen hblen hilen hnd (hsj ▸ rfl) hreg hrarg
    (hsj ▸ hsclosed j h) (hsj ▸ hsrcfv j h) (hfclosed j) (fun x => hffv x j)
    hoclosed hclose ?_ hnest hsrcfv hsclosed hopen
  -- `hlink`: the block map names the block's own ids, and `Γ` records the block at the
  -- matching index. This is where the two halves of the agreement meet.
  intro nm x hx
  obtain ⟨k, hk, hnm, hid⟩ := hfv nm x hx
  exact ⟨k, hilen ▸ hk, hid, hnm ▸ hreg k hk⟩

/-- **`RecEnvConsistent` for one walked block** (slice δ-D8) — what
`EnvErasureRec.recEnvConsistent_of_registeredClosureRec` used to buy from the certificate,
now bought from the run plus the agreement.

`hcov` is the other direction of the same agreement `erases_rec_block_of_run`'s `hreg` is
one half of: every constant `Γ` records as recursive is a member of *this* block. At a
single-block cold start that is the whole of `Γ.recBodies`; a `Γ` describing several
blocks needs the per-block records combined, which is a `List`-level fold and not a new
idea. -/
theorem recEnvConsistent_of_block {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {Esrc : SEnv} {fixnames : List Name} {srcs : List Expr}
    {defs : List (@FixDef LBTerm)} {sd : ErasureState}
    (hslen : srcs.length = defs.length) (hnlen : fixnames.length = defs.length)
    (hkeys : KeysDistinct (recConstState fixnames defs sd).gdecls)
    (hkn : ∀ j (h : j < defs.length),
        Γ.constants (fixnames[j]'(hnlen ▸ h)) = toKername (fixnames[j]'(hnlen ▸ h)))
    (hdisj : ∀ j (h : j < defs.length),
        Γ.ctors (fixnames[j]'(hnlen ▸ h)) = none ∧
          Γ.casesOns (fixnames[j]'(hnlen ▸ h)) = none)
    (hesrc : ∀ j (h : j < defs.length),
        Esrc (fixnames[j]'(hnlen ▸ h)) = some (srcs[j]'(hslen ▸ h)))
    (her : ∀ j (h : j < defs.length) (Δ : VLCtx),
        Erases env Us Γ Δ (srcs[j]'(hslen ▸ h)) (.fix defs j))
    (hcov : ∀ {n : Name} {d : List (@FixDef LBTerm)} {i : Nat},
        Γ.recBodies n = some (d, i) →
        ∃ h : i < defs.length, (fixnames[i]'(hnlen ▸ h)) = n ∧ d = defs) :
    RecEnvConsistent env Us Γ Esrc (recConstState fixnames defs sd).gdecls where
  reg := by
    intro n d i hrec
    obtain ⟨hi, hnm, rfl⟩ := hcov hrec
    subst hnm
    refine ⟨?_, (hdisj i hi).1, (hdisj i hi).2, _, hesrc i hi, fun {Δ} => her i hi Δ⟩
    rw [hkn i hi]
    refine recConstState_envLookup ?_ hkeys
    have hz : (fixnames.zipIdx[i]'(by simpa using hnlen ▸ hi)) =
        ((fixnames[i]'(hnlen ▸ hi)), i) := by simp
    exact hz ▸ List.getElem_mem _

/-! ## Assembling `RegisteredClosureData` from the walk

The per-call fact above is about **one** constant. Turning it into the closure-level
record the capstones consume needs three further inputs, each of which is a genuine
parameter-side obligation rather than something the run can supply:

* **context-uniformity** — `ErasesEnvDeltaData` unfolds a constant at an arbitrary `Δ`,
  while the bridge fires at the `Δ = []` the run actually uses. Lifting needs a weakening
  lemma for `Erases` over a closed subject, which this development does not have (`Erases`
  has `abstract`/`uninstantiate`/`thin_vlet`, all context-*shrinking*);
* **applied form** (`NoBlock`) of the stored body — a statement about the run's output
  that the output-shape induction does not prove (it proves `NoFix`/`LBClosed`);
* **domain agreement** — that `Esrc`'s domain is exactly what the walk registered, and
  that `Esrc`'s constants are not `Γ`-registered constructors or `casesOn` heads
  (`RegisteredClosureData.disj`).

They appear as the explicit `hdisj`/`huni`/`hnb`/`hEsrc` premises of the walk step below,
named one per row, so that a consumer sees exactly what it is buying. -/

/-- **`RegisteredClosureData` at an empty source environment.** The degenerate — and, at
cold start, the *operative* — case: with no source constants there is nothing to register,
so the record holds at any `E`.

It was more than a convenience before slice D4a: the cold-start bridge invariant's
`known_dom` field forced `known = ⊥` at the empty state (nothing is registered yet) and
`Supported.const` needs `known n`, so the cold-start fragment contained no δ-constant at
all. That field is now deleted, the bridge fires at a non-empty fragment, and slice D5
un-pinned the capstones too (`registeredClosureData_of_deltaMem_walked` below is what they
call instead). This stays as the degenerate case it always was. -/
theorem registeredClosureData_empty {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {E : GlobalDeclarations} : RegisteredClosureData env Us Γ (fun _ => none) E where
  disj := by intro n body h; exact absurd h (by simp)
  erase := by intro n body h; exact absurd h (by simp)

/-- **`RegisteredClosureData` transports along the walk.** The record established at an
intermediate state survives to the final one — key distinctness of the final `gdecls` is
what keeps the established entries from being shadowed. -/
theorem RegisteredClosureData.mono {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {Esrc : SEnv} {s s' : ErasureState}
    (h : RegisteredClosureData env Us Γ Esrc s.gdecls)
    (hle : StateLe s s') (hkeys : KeysDistinct s'.gdecls) :
    RegisteredClosureData env Us Γ Esrc s'.gdecls where
  disj := h.disj
  erase := by
    intro n body hunf
    obtain ⟨body', hlook, her, hnb⟩ := h.erase hunf
    exact ⟨body', envLookup_mono_stateLe hle hkeys hlook, her, hnb⟩

/-- **One walk step, δ half.** Extending the record with the constant a non-recursive
`visitMutual` exit has just registered: the new constant's witness is
`erases_nonrec_const_registered`, the old ones survive by `RegisteredClosureData.mono`.

`hEsrc` is the domain agreement at this one name (the body `Esrc` records for `n` is the
body the run erased — the *prepared* one, which is the convention
`RegisteredClosure`'s docstring fixes), `huni`/`hnb` are the two output-side residues. -/
theorem registeredClosureData_step_nonrec {env : VEnv} {Us : List Name}
    {known : Name → Prop} {Γ : ErasureCtx} {Esrc : SEnv}
    {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
    (Hδ : ∀ (cc : Core.Context) (rf : ST.Ref IO.RealWorld Core.State),
      DeltaHyps env Us known Γ Esrc gw cc rf)
    (henv : env.Ordered) (hknames : ∀ m : Name, Γ.constants m = toKername m)
    {n : Name} {pe : Expr} {t : LBTerm} {sp st s s₁ : ErasureState}
    {ctx' : ErasureContext} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {wp wt : Void IO.RealWorld}
    (hold : RegisteredClosureData env Us Γ Esrc s.gdecls)
    (hle : StateLe s s₁) (hkeys : KeysDistinct s₁.gdecls)
    (hvis : Erasure.visitExpr pe sp ctx' cctx ref wp = .ok (t, st) wt)
    (hinv : BridgeInv env Us known Γ (gw wp) ctx' sp [])
    (hsupp : Supported known Γ pe) (hex : ∃ ve, TrExprS env Us [] pe ve)
    (hpost : InlineExt (nonrecConstState n t st) s₁)
    (hdisj : Γ.ctors n = none ∧ Γ.casesOns n = none)
    (hEsrc : ∀ {body : Expr}, Esrc n = some body → body = pe)
    (huni : ∀ {Δ : VLCtx}, Erases env Us Γ [] pe t → Erases env Us Γ Δ pe t)
    (hnb : NoBlock t) :
    RegisteredClosureData env Us Γ Esrc s₁.gdecls where
  disj := hold.disj
  erase := by
    intro m body hunf
    by_cases hm : m = n
    · subst hm
      obtain rfl : body = pe := hEsrc hunf
      obtain ⟨hlook, her, -, -⟩ :=
        erases_nonrec_const_registered H HD C Hδ henv hknames hvis hinv hsupp hex hpost
      exact ⟨t, hlook, fun {Δ} => huni (Δ := Δ) her, hnb⟩
    · obtain ⟨body', hlook, her, hnbb⟩ := hold.erase hunf
      exact ⟨body', envLookup_mono_stateLe hle hkeys hlook, her, hnbb⟩

/-! ## From the walk's record to the capstone's — the conversion (slice D4b)

`DeltaMem` (`DeltaHyps.lean`) is what the bridge now *carries*: every constant body the
walk recorded for a fragment name erases the source body `Esrc` records for it. Membership
in `gdecls`, not `envLookup`, is what makes it survive the walk (S1e's refutation:
`KeysDistinct` cannot be carried by a state predicate), so the conversion happens once,
here, at the final state — which is also where `KeysDistinct` is a capstone premise anyway.

Three halves the record deliberately does **not** carry, each a premise below and each for
a reason that is not an oversight:

* **existence** (`hreg`) — the walk registered a body for every fragment constant it
  reached. That is a *reachability* fact about the source program, not about the erasure;
  the record is keyed on the entry precisely so that `register_inductive`'s `@[extern]`
  axiom prefix (which grows the registry domain without recording a body) transports for
  free. `DeltaHyps.axiom_free` is what will rule out the axiom-emitted names when a
  capstone discharges this.
* **context uniformity** (`huni`) — the bridge fires at the `Δ` of the call site, and
  `RegisteredClosure` quantifies over all `Δ`. This is the same `huni` residue
  `registeredClosureData_step_nonrec` carries, and it is a lean4lean-side `TrExprS`
  weakening obligation, not an erasure one.
* **applied form** (`hnb`, the `Data` version only) — `NoBlock` of the stored body is an
  output-shape statement about `visitExpr`; the shape induction proves `NoFix`/`LBClosed`
  and not this, and inside the bridge the erasure argument is abstract, so no motive can
  conclude it. It is `ColdStartSubject.noBlock`'s job, widened to every reader context. -/

/-- **The walk's δ record becomes the capstone's** (β + δ flavour). -/
theorem registeredClosure_of_deltaMem {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {Esrc : SEnv} {s : ErasureState}
    (h : DeltaMem env Us Γ Esrc s) (hkeys : KeysDistinct s.gdecls)
    (hdisj : ∀ {n : Name} {body : Expr}, Esrc n = some body →
      Γ.ctors n = none ∧ Γ.casesOns n = none)
    (hreg : ∀ {n : Name} {body : Expr}, Esrc n = some body →
      ∃ t : LBTerm, (Γ.constants n, GlobalDecl.constantDecl ⟨some t⟩) ∈ s.gdecls)
    (huni : ∀ {n : Name} {body : Expr} {t : LBTerm} {Δ Δ' : VLCtx}, Esrc n = some body →
      VLCtx.WF env Us.length Δ → Δ.NoBV →
      Erases env Us Γ Δ body t → Erases env Us Γ Δ' body t) :
    RegisteredClosure env Us Γ Esrc s.gdecls where
  disj := hdisj
  erase := by
    intro n body hb
    obtain ⟨t, hmem⟩ := hreg hb
    obtain ⟨Δ, hΔwf, hΔnb, her⟩ := h.erase hb hmem
    exact ⟨t, envLookup_of_mem_of_keys hmem hkeys, fun {_} => huni hb hΔwf hΔnb her⟩

/-- **The walk's δ record becomes the capstone's** (data flavour): the same conversion,
plus the applied-form conjunct the data simulation consumes. -/
theorem registeredClosureData_of_deltaMem {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {Esrc : SEnv} {s : ErasureState}
    (h : DeltaMem env Us Γ Esrc s) (hkeys : KeysDistinct s.gdecls)
    (hdisj : ∀ {n : Name} {body : Expr}, Esrc n = some body →
      Γ.ctors n = none ∧ Γ.casesOns n = none)
    (hreg : ∀ {n : Name} {body : Expr}, Esrc n = some body →
      ∃ t : LBTerm, (Γ.constants n, GlobalDecl.constantDecl ⟨some t⟩) ∈ s.gdecls)
    (huni : ∀ {n : Name} {body : Expr} {t : LBTerm} {Δ Δ' : VLCtx}, Esrc n = some body →
      VLCtx.WF env Us.length Δ → Δ.NoBV →
      Erases env Us Γ Δ body t → Erases env Us Γ Δ' body t)
    (hnb : ∀ {kn : Kername} {t : LBTerm},
      (kn, GlobalDecl.constantDecl ⟨some t⟩) ∈ s.gdecls → NoBlock t) :
    RegisteredClosureData env Us Γ Esrc s.gdecls where
  disj := hdisj
  erase := by
    intro n body hb
    obtain ⟨t, hmem⟩ := hreg hb
    obtain ⟨Δ, hΔwf, hΔnb, her⟩ := h.erase hb hmem
    exact ⟨t, envLookup_of_mem_of_keys hmem hkeys, fun {_} => huni hb hΔwf hΔnb her, hnb hmem⟩

/-! ## The walk-restricted source environment (slice D5)

The conversion above takes *three* premises the walk does not supply — existence
(`hreg`), key distinctness (`hkeys`, i.e. `hkinj`) and applied form (`hnb`) — and the
first two are artefacts of asking the wrong question. `ErasesEnvDeltaData` quantifies over
**all** of `Esrc`'s domain, while the walk only registers the constants it actually
*reached*; a fragment constant the program never mentions is never registered, so the
unrestricted record is not merely unproved, it is **false**. Proving reachability ("an
evaluation only touches walked constants") is a large detour and, worse, it is a property
of the source program rather than of the erasure.

**Restrict instead.** `SEnv.walked` cuts `Esrc` down to the constants for which the run's
final environment really stores a body, and then

* **existence is by construction** — the restriction's own defining condition *is* the
  lookup the record needs;
* **key distinctness disappears** — the restriction is keyed on `LBTerm.envLookup`, the
  first-match-wins lookup the target semantics actually uses, so the conversion never has
  to turn a membership into a lookup and never needs `KeysDistinct`. (`DeltaMem` is keyed
  on membership because that is what survives the walk; the *inclusion* it needs here goes
  the easy way, `envLookup_mem`.)

What the restriction costs is paid by the consumer, in the right place: the capstone's
source-evaluation premise becomes "`pe` evaluates using only the constants the walk
recorded", which is exactly the honest side condition, is monotone (an evaluation in the
restricted environment is one in the full environment), and is where a two-declaration
cold start has to be checked anyway. -/

/-- `Esrc` restricted to the constants a run's final environment stores a **body** for.

Keyed on `LBTerm.envLookup` rather than on membership in `gdecls`, and rather than on the
registry domain `s.constants`, for two independent reasons: `envLookup` is the target
semantics' own δ-lookup, so the restriction says precisely "the δ step this environment can
actually take"; and the registry domain also grows at `addAxiom` (both `visitMutual`'s
value-less exits and `register_inductive`'s `@[extern]`-constructor prefix), which records
no body at all. -/
def SEnv.walked (Esrc : SEnv) (Γ : ErasureCtx) (E : GlobalDeclarations) : SEnv :=
  fun n => match LBTerm.envLookup E (Γ.constants n) with
    | some (.constantDecl ⟨some _⟩) => Esrc n
    | _ => none

/-- The restriction only forgets: it never invents an unfolding. -/
theorem SEnv.walked_le {Esrc : SEnv} {Γ : ErasureCtx} {E : GlobalDeclarations} {n : Name}
    {body : Expr} (h : Esrc.walked Γ E n = some body) : Esrc n = some body := by
  unfold SEnv.walked at h
  split at h
  · exact h
  · exact absurd h (by simp)

/-- An empty fragment restricts to an empty fragment — what keeps the δ-free capstone
guards reading as they did before slice D5. -/
@[simp] theorem SEnv.walked_bot (Γ : ErasureCtx) (E : GlobalDeclarations) :
    SEnv.walked (fun _ => none) Γ E = fun _ => none := by
  funext n; unfold SEnv.walked; split <;> rfl

/-- **What the restriction hands back**: for a name it keeps, the environment's stored
body — the `envLookup` half of `RegisteredClosure*.erase`, for free. -/
theorem SEnv.walked_lookup {Esrc : SEnv} {Γ : ErasureCtx} {E : GlobalDeclarations}
    {n : Name} {body : Expr} (h : Esrc.walked Γ E n = some body) :
    ∃ t : LBTerm, LBTerm.envLookup E (Γ.constants n) = some (.constantDecl ⟨some t⟩) := by
  unfold SEnv.walked at h
  split at h
  · rename_i t hlk; exact ⟨t, hlk⟩
  · exact absurd h (by simp)

/-- **Applied form of every stored body.** Every `.constantDecl` the walk recorded with a
value holds a term in applied form.

This was residue 3 and is now a theorem (`visitExpr_noBlockEnv`, below). The obstruction
the ledger recorded — "`NoBlock` is not an invariant the shape induction can carry" — was a
misdiagnosis: `NoBlock` says nothing about boxing, it forbids exactly one node
(`.construct _ _ (_ :: _)`), and the eraser's single `.construct` construction site is
nullary by explicit design. So the shape induction carries it as `ShapeC`'s third conjunct,
and this predicate is the environment-level fold of that fact rather than a premise. -/
def NoBlockEnv (E : GlobalDeclarations) : Prop :=
  ∀ {kn : Kername} {t : LBTerm}, (kn, GlobalDecl.constantDecl ⟨some t⟩) ∈ E → NoBlock t

/-! ### `NoBlockEnv` is a `RunClosed` predicate (slice δ-N)

The five registration-side slots are free, one per way the walk touches `gdecls`:
`inl` leaves `gdecls` alone; `addAxiom` conses a **value-less** entry
(`Erasure.addAxiomState`); `register_inductive` conses an `.inductiveDecl` on top of a
`ConstExt` prefix that is entirely value-less axiom entries, and its hit branch is
state-preserving; and the two constant conses are exactly where the widened
`RunClosed.nrc`/`rc` now hand over the `NoBlock` of the body being stored.

Only `prep` is assumed, and it is the standing `PrepareHyps`-class item every `RunClosed`
instantiation pays: `prepare_erasure`'s csimp branch runs `Lean.Core.transform` at `EraseM`
through `MonadControlT`, so state transparency does not follow from the `liftM` lemmas.
`DeltaHyps.prep_run` states it (as `s' = s`), which is why the capstones can feed this
from a bundle they already carry rather than from a new premise. -/

/-- The block registration's fold, one cons at a time: `recConstState` stores
`.fix defs j` under each of the block's names, so a `NoBlock` environment stays one exactly
when every index of the block is in applied form — which `NoBlock_fix`'s
index-independence makes a single fact. -/
theorem noBlockEnv_recConstState {names : List Name} {defs : List (@FixDef LBTerm)}
    {s : ErasureState} (h : NoBlockEnv s.gdecls) (hnb : ∀ j : Nat, NoBlock (.fix defs j)) :
    NoBlockEnv (recConstState names defs s).gdecls := by
  rw [recConstState_eq]
  generalize names.zipIdx = L
  induction L generalizing s with
  | nil => exact h
  | cons p rest ih =>
    refine ih ?_
    intro kn t hm
    simp only [recConstStep, nonrecConstState] at hm
    rcases List.mem_cons.mp hm with heq | hm'
    · obtain ⟨-, hd⟩ : kn = toKername p.1 ∧
          GlobalDecl.constantDecl ⟨some t⟩
            = GlobalDecl.constantDecl ⟨some (LBTerm.fix defs p.2)⟩ := by simpa using heq
      obtain rfl : t = LBTerm.fix defs p.2 := by simpa using hd
      exact hnb p.2
    · exact h hm'

/-- **`NoBlockEnv` of the registry is `RunClosed`** — the retirement of
`ColdStartSubject.noBlockEnv`. See the section docstring for the slot-by-slot accounting;
`hprep` is the one assumed slot and is `DeltaHyps.prep_run` at every capstone. -/
theorem runClosed_noBlockEnv
    (hprep : ∀ {e : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
        {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {pe : Expr}
        {s' : ErasureState} {w' : Void IO.RealWorld},
      prepare_erasure e s ctx cctx ref w = .ok (pe, s') w' → s'.gdecls = s.gdecls) :
    RunClosed (fun s => NoBlockEnv s.gdecls) where
  inl := fun h => h
  ax := by
    intro m s ctx cctx ref w u s' w' hrun h
    obtain ⟨rfl, -⟩ := run_addAxiom_ok hrun
    intro kn t hm
    simp only [addAxiomState] at hm
    rcases List.mem_cons.mp hm with heq | hm'
    · exact absurd heq (by simp)
    · exact h hm'
  reg := by
    intro ii s ctx cctx ref w r s' w' hrun h
    cases hi : s.inductives.get? ii.name with
    | some rc0 =>
      obtain ⟨-, rfl, -⟩ := run_register_inductive_hit_ok hi hrun
      exact h
    | none =>
      obtain ⟨bodies, sM, rfl, -, -, hext, -, -⟩ := run_register_inductive_cold_ok hi hrun
      intro kn t hm
      simp only [registerIndState] at hm
      rcases List.mem_cons.mp hm with heq | hm'
      · exact absurd heq (by simp)
      · obtain ⟨pre, hpre, hax⟩ := hext.gdecls
        rw [hpre] at hm'
        rcases List.mem_append.mp hm' with hp | hp
        · exact absurd (hax _ hp).1 (by simp)
        · exact h hp
  prep := fun hrun h => by rw [hprep hrun]; exact h
  nrc := by
    intro n t s h hnf hcl hnb
    intro kn t' hm
    simp only [nonrecConstState] at hm
    rcases List.mem_cons.mp hm with heq | hm'
    · obtain ⟨-, hd⟩ : kn = toKername n ∧
          GlobalDecl.constantDecl ⟨some t'⟩ = GlobalDecl.constantDecl ⟨some t⟩ := by
        simpa using heq
      obtain rfl : t' = t := by simpa using hd
      exact hnb
    · exact h hm'
  rc := fun h _ hnb => noBlockEnv_recConstState h hnb

/-- **Every body a whole `visitExpr` run recorded is in applied form** — what
`ColdStartSubject.noBlockEnv` used to assume, now derived from the run. -/
theorem visitExpr_noBlockEnv
    (hprep : ∀ {e : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
        {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {pe : Expr}
        {s' : ErasureState} {w' : Void IO.RealWorld},
      prepare_erasure e s ctx cctx ref w = .ok (pe, s') w' → s'.gdecls = s.gdecls)
    {e : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {t : LBTerm}
    {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w')
    (h : NoBlockEnv s.gdecls) : NoBlockEnv s'.gdecls :=
  (visitExpr_output_shape (runClosed_noBlockEnv hprep) hrun h).1

/-- At the empty state there is nothing recorded, so the environment is trivially in
applied form — which is what makes the capstones' instantiation free. -/
@[simp] theorem noBlockEnv_empty : NoBlockEnv ({} : ErasureState).gdecls := by
  intro kn t hm; simp at hm

/-- **The walk's δ record becomes the capstone's, at the walk-restricted `Esrc`** (β + δ
flavour). Compared with `registeredClosure_of_deltaMem` the existence premise `hreg` and
the key-distinctness premise `hkeys` are **gone** — `SEnv.walked`'s defining condition
supplies the first and *is* a lookup, so the second is not needed. What survives is the
context-uniformity premise `huni`, which the capstones now discharge with
`ErasesUniform.erases_uniform_closed`. -/
theorem registeredClosure_of_deltaMem_walked {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {Esrc : SEnv} {s : ErasureState} (h : DeltaMem env Us Γ Esrc s)
    (hdisj : ∀ {n : Name} {body : Expr}, Esrc n = some body →
      Γ.ctors n = none ∧ Γ.casesOns n = none)
    (hclenv : ClosedEnv s.gdecls)
    (huni : ∀ {n : Name} {body : Expr} {t : LBTerm} {Δ Δ' : VLCtx}, Esrc n = some body →
      (Γ.constants n, GlobalDecl.constantDecl ⟨some t⟩) ∈ s.gdecls → LBClosed t 0 →
      VLCtx.WF env Us.length Δ → Δ.NoBV →
      Erases env Us Γ Δ body t → Erases env Us Γ Δ' body t) :
    RegisteredClosure env Us Γ (Esrc.walked Γ s.gdecls) s.gdecls where
  disj := fun hb => hdisj (SEnv.walked_le hb)
  erase := by
    intro n body hb
    obtain ⟨t, hlk⟩ := SEnv.walked_lookup hb
    obtain ⟨k, hmem, hbeq⟩ := envLookup_mem hlk
    obtain rfl := Kername.eq_of_beq hbeq
    obtain ⟨Δ, hΔwf, hΔnb, her⟩ := h.erase (SEnv.walked_le hb) hmem
    exact ⟨t, hlk, fun {_} => huni (SEnv.walked_le hb) hmem (hclenv hlk) hΔwf hΔnb her⟩

/-- **The walk's δ record becomes the capstone's, at the walk-restricted `Esrc`** (data
flavour): the same conversion, plus the applied-form conjunct the data simulation
consumes. `hnb` is the one premise `SEnv.walked` cannot retire — see `NoBlockEnv`. -/
theorem registeredClosureData_of_deltaMem_walked {env : VEnv} {Us : List Name}
    {Γ : ErasureCtx} {Esrc : SEnv} {s : ErasureState} (h : DeltaMem env Us Γ Esrc s)
    (hdisj : ∀ {n : Name} {body : Expr}, Esrc n = some body →
      Γ.ctors n = none ∧ Γ.casesOns n = none)
    (hclenv : ClosedEnv s.gdecls)
    (huni : ∀ {n : Name} {body : Expr} {t : LBTerm} {Δ Δ' : VLCtx}, Esrc n = some body →
      (Γ.constants n, GlobalDecl.constantDecl ⟨some t⟩) ∈ s.gdecls → LBClosed t 0 →
      VLCtx.WF env Us.length Δ → Δ.NoBV →
      Erases env Us Γ Δ body t → Erases env Us Γ Δ' body t)
    (hnb : NoBlockEnv s.gdecls) :
    RegisteredClosureData env Us Γ (Esrc.walked Γ s.gdecls) s.gdecls where
  disj := fun hb => hdisj (SEnv.walked_le hb)
  erase := by
    intro n body hb
    obtain ⟨t, hlk⟩ := SEnv.walked_lookup hb
    obtain ⟨k, hmem, hbeq⟩ := envLookup_mem hlk
    obtain rfl := Kername.eq_of_beq hbeq
    obtain ⟨Δ, hΔwf, hΔnb, her⟩ := h.erase (SEnv.walked_le hb) hmem
    exact ⟨t, hlk, fun {_} => huni (SEnv.walked_le hb) hmem (hclenv hlk) hΔwf hΔnb her, hnb hmem⟩

/-- **`SEnvConsistent` restricts.** The source-side δ trust item is a `∀` over `Esrc`'s
domain, so cutting the domain down keeps it — which is what lets the capstone state its
evaluation premise at the walk-restricted environment while taking the trust item at the
fragment's own. -/
theorem SEnvConsistent.walked {env : VEnv} {Us : List Name} {Esrc : SEnv} {Γ : ErasureCtx}
    {E : GlobalDeclarations} (h : SEnvConsistent env Us Esrc) :
    SEnvConsistent env Us (Esrc.walked Γ E) :=
  fun hb htr => h (SEnv.walked_le hb) htr

/-! ## Non-vacuity

The bridge-facing results here inherit their guards from `erases_nonrec_const_body`
(whose premise set is guarded in `EnvErasureNonrec`/`VisitExprRefines`) and from the run,
which is hypothetical everywhere in this development. What *is* constructible, and is
built below, is the environment plumbing: the membership-to-lookup step and the recursive
block's registration, on a concrete two-name block — so neither is true merely because
`gdecls` is empty or the keys never separate. -/

/-- A concrete two-definition block. -/
private def gRecDefs : List (@FixDef LBTerm) :=
  [{ name := .named "f", body := .bvar 0 }, { name := .named "g", body := .bvar 1 }]

/-- The two keys the block registration conses are `beq`-distinct, so the fold really
does produce a key-distinct environment. -/
private theorem gRecKeys : KeysDistinct (recConstState [`f, `g] gRecDefs {}).gdecls := by
  refine List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  subst hq
  decide

/-- Non-vacuity: both siblings of a genuinely registered recursive block are found by
`LBTerm.envLookup`, each at its own index — the `envLookup` conjunct of
`RegisteredClosureRec.erase`/`RecEnvConsistent.reg`, on real data. -/
theorem gRecConstState_lookups :
    LBTerm.envLookup (recConstState [`f, `g] gRecDefs {}).gdecls (toKername `f)
        = some (.constantDecl ⟨some (.fix gRecDefs 0)⟩) ∧
    LBTerm.envLookup (recConstState [`f, `g] gRecDefs {}).gdecls (toKername `g)
        = some (.constantDecl ⟨some (.fix gRecDefs 1)⟩) :=
  ⟨recConstState_envLookup (by simp) gRecKeys, recConstState_envLookup (by simp) gRecKeys⟩

/-- **The δ record is non-vacuous on real data**: a one-entry environment in which the
fragment's constant `f` really is recorded, and the recorded body really erases the body
`Esrc` gives it (`Erases.bvar`, a rule with no typing premise, so the witness is fully
constructed). Both of `DeltaMem.erase`'s premises are inhabited here — the record is not
true merely because `gdecls` is empty or `Esrc` is `⊥`. -/
theorem gDeltaMem (env : VEnv) (Us : List Name) :
    DeltaMem env Us gΓδ (gEsrcδ (.bvar 0))
      { ({} : ErasureState) with
        gdecls := [(toKername `f, .constantDecl ⟨some (.bvar 0)⟩)] } where
  erase := by
    intro n body t hb hm
    have hn : n = `f := by
      by_cases h : n = `f
      · exact h
      · simp [gEsrcδ, h] at hb
    subst hn
    obtain rfl : body = .bvar 0 := by simpa [gEsrcδ] using hb.symm
    obtain rfl : t = .bvar 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      simpa using (by simpa using hm : gΓδ.constants `f = toKername `f ∧ t = LBTerm.bvar 0).2
    exact ⟨[], trivial, rfl, .bvar 0⟩

/-- Non-vacuity: the *later*-consed sibling does not shadow the earlier one — which is
what `envLookup_of_mem_of_keys` buys, and what a caller's `KeysDistinct` premise is for. -/
theorem gRecConstState_no_shadow :
    LBTerm.envLookup (recConstState [`f, `g] gRecDefs {}).gdecls (toKername `f)
      ≠ LBTerm.envLookup (recConstState [`f, `g] gRecDefs {}).gdecls (toKername `g) := by
  rw [gRecConstState_lookups.1, gRecConstState_lookups.2]
  simp [gRecDefs]

/-! ### The recursive-dependency guard (slice δ-D8)

The chain the slice builds, run end to end on the repo's own recursion fixture — the
genuinely self-referential one-def block `def f (a : Prop) := f a` (`Erases.lean`'s
`fixRecSrc`/`fixRecDefs`/`ΓfixRec`), at its two stages:

* the **open** stage, `λa. x #0`, where the sibling still sits as the fresh fixvar the run
  minted and the derivation lives at the block-local `ΓfixRec.withFixvars {f ↦ x}` — which
  is `ΓfixOpen x` on the nose. That is the shape
  `VisitExprRefines.visitExpr_refines_erases_block` produces from a sibling's `visitExpr`
  run, and the guard there checks its premise set is jointly instantiable at exactly this
  `Γ`;
* the **closed** stage, `fix f. λa. f a`, which is what the walk stores.

`erases_rec_block_of_run` carries the first to the second, and `recEnvConsistent_of_block`
turns that into the environment-level record the forward simulations consume — at a `Γ`
that genuinely registers recursion and an `Esrc` that genuinely records the body, so
neither is true by emptiness.

One premise stays hypothetical, and it is not new: `hnest`, the residue
`Erases.instFixvars` has carried since W3.1 and which `EnvErasureRec.gErases_fix_of_open`
already leaves open for the same reason (the repaired theorem pins `Γ.fixvars = ⊥`, so the
older guards' dodge — taking the outer `Γ` to be the block-local one, where `hnest` is
`id` — is gone). Everything else is constructed. -/

/-- The block-local fixvar map `visitMutual` installs for the fixture's one-def block. -/
private def gFvD8 (x : FVarId) : Name → Option FVarId :=
  fun n => if n = `f then some x else none

/-- The run's **opened** target body: `λa. x #0`, before `mkDef` closes the fixvar. -/
private def gObodyD8 (x : FVarId) : LBTerm :=
  .lambda (nameToBinder `a) (.app (.fvar x) (.bvar 0))

/-- `mkDef`'s closing really does turn the opened body into the stored block's body. -/
private theorem gCloseD8 (x : FVarId) :
    (fixRecDefs[0]'(by simp [fixRecDefs])).body = closeFix [x] 0 (gObodyD8 x) := by
  rw [closeFix_cons]
  simp [fixRecDefs, gObodyD8, closeFix, toBvar]

/-- **The composition fires**: from the block-local erasure of the sibling body — the
`Γ.withFixvars fv` stage, which is what the instantiated bridge hands back — to the
`Erases.fix` derivation at the outer `Γ`, at **every** context. -/
theorem gErasesRecBlockD8 (env : VEnv) (henv : env.Ordered) (Us : List Name) (x : FVarId)
    (hnest : ∀ {Δ' : VLCtx} {n' : Name} {ty' b' : Expr} {bi' : BinderInfo}
        {d' : List (@FixDef LBTerm)} {i' : Nat},
        Erases env Us (ΓfixRec.withFixvars (gFvD8 x)) Δ' (.lam n' ty' b' bi') (.fix d' i') →
        Erases env Us ΓfixRec Δ' (.lam n' ty' b' bi') (.fix d' i')) :
    ∀ Δ : VLCtx, Erases env Us ΓfixRec Δ fixRecSrc (.fix fixRecDefs 0) := by
  intro Δ
  refine erases_rec_block_of_run henv (Γ := ΓfixRec) rfl (fv := gFvD8 x)
    (fixnames := [`f]) (ids := [x]) (srcs := [fixRecSrc]) (obodies := [gObodyD8 x])
    (defs := fixRecDefs) rfl rfl rfl rfl (by simp) (fun j h => ?_) (fun nm y hy => ?_)
    (fun d hd => ?_) (fun j => ?_) (fun j h => ?_) (fun j h => ?_) (fun j h => ?_)
    (fun j h => ?_) (fun j h => ?_) (fun j h => ?_) hnest 0 (by simp [fixRecDefs]) Δ
  · -- hreg
    obtain rfl : j = 0 := by simp only [fixRecDefs, List.length_cons, List.length_nil] at h; omega
    exact ΓfixRec_recBodies
  · -- hfv: the block map names the block's own id, at index 0
    refine ⟨0, by simp [fixRecDefs], ?_, ?_⟩ <;>
      · by_cases hf : nm = `f <;> simp_all [gFvD8]
  · -- hrarg
    simp only [fixRecDefs, List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd; rfl
  · -- the stored block is de Bruijn closed
    show LBClosed (LBTerm.fix fixRecDefs j) 0
    simp [fixRecDefs, LBClosedDefs]
  · -- the opened body is de Bruijn closed
    obtain rfl : j = 0 := by simp only [fixRecDefs, List.length_cons, List.length_nil] at h; omega
    show LBClosed (gObodyD8 x) 0
    simp [gObodyD8]
  · -- hclose
    obtain rfl : j = 0 := by simp only [fixRecDefs, List.length_cons, List.length_nil] at h; omega
    exact gCloseD8 x
  · -- the source is a λ-telescope
    obtain rfl : j = 0 := by simp only [fixRecDefs, List.length_cons, List.length_nil] at h; omega
    exact ⟨_, _, _, _, rfl⟩
  · -- …closed
    obtain rfl : j = 0 := by simp only [fixRecDefs, List.length_cons, List.length_nil] at h; omega
    exact ⟨trivial, trivial, Nat.zero_lt_one⟩
  · -- …and fvar-free
    obtain rfl : j = 0 := by simp only [fixRecDefs, List.length_cons, List.length_nil] at h; omega
    exact ⟨rfl, by simp [FVarsIn], trivial⟩
  · -- hopen: the block-local erasure, through the `Erases.fixvar` leaf
    obtain rfl : j = 0 := by simp only [fixRecDefs, List.length_cons, List.length_nil] at h; omega
    show Erases env Us (ΓfixRec.withFixvars (gFvD8 x)) [] fixRecSrc (gObodyD8 x)
    exact .lam (ty' := .sort .zero) (.sort rfl)
      (.app (erases_fixvar_fixOpen env Us x [] _ (by simp)) (.bvar 0))

/-- The fixture's source environment: `f` unfolds to the recursive body. -/
private def gEsrcD8 : SEnv := fun n => if n = `f then some fixRecSrc else none

/-- The one-entry environment the block registration conses has distinct keys. -/
private theorem gKeysD8 : KeysDistinct (recConstState [`f] fixRecDefs {}).gdecls := by
  simp [recConstState, KeysDistinct]

/-- **`RecEnvConsistent` from the walk, for a recursive block** (slice δ-D8) — the
demotion of `EnvErasureRec.RegisteredClosureRec` on real data. Nothing here is a
certificate about an erasure: the `Erases` witness is *derived* through
`erases_rec_block_of_run`, and what is left assumed is the `Γ`↔run registration
agreement (`hcov`, discharged here by `ΓfixRec`'s own defining equation) and `hnest`. -/
theorem gRecEnvConsistentD8 (env : VEnv) (henv : env.Ordered) (Us : List Name) (x : FVarId)
    (hnest : ∀ {Δ' : VLCtx} {n' : Name} {ty' b' : Expr} {bi' : BinderInfo}
        {d' : List (@FixDef LBTerm)} {i' : Nat},
        Erases env Us (ΓfixRec.withFixvars (gFvD8 x)) Δ' (.lam n' ty' b' bi') (.fix d' i') →
        Erases env Us ΓfixRec Δ' (.lam n' ty' b' bi') (.fix d' i')) :
    RecEnvConsistent env Us ΓfixRec gEsrcD8 (recConstState [`f] fixRecDefs {}).gdecls := by
  refine recEnvConsistent_of_block (fixnames := [`f]) (srcs := [fixRecSrc]) rfl rfl gKeysD8
    (fun j h => ?_) (fun j h => ?_) (fun j h => ?_)
    (fun j h Δ => by
      obtain rfl : j = 0 := by
        simp only [fixRecDefs, List.length_cons, List.length_nil] at h; omega
      exact gErasesRecBlockD8 env henv Us x hnest Δ)
    (fun {n d i} hrec => ?_)
  · obtain rfl : j = 0 := by simp only [fixRecDefs, List.length_cons, List.length_nil] at h; omega
    rfl
  · obtain rfl : j = 0 := by simp only [fixRecDefs, List.length_cons, List.length_nil] at h; omega
    exact ⟨rfl, rfl⟩
  · obtain rfl : j = 0 := by simp only [fixRecDefs, List.length_cons, List.length_nil] at h; omega
    simp [gEsrcD8]
  · by_cases hn : n = `f
    · subst hn
      obtain ⟨rfl, rfl⟩ : d = fixRecDefs ∧ i = 0 := by
        have := (by simpa [ΓfixRec] using hrec : fixRecDefs = d ∧ 0 = i)
        exact ⟨this.1.symm, this.2.symm⟩
      exact ⟨by simp [fixRecDefs], rfl, rfl⟩
    · simp [ΓfixRec, hn] at hrec

end LeanToLambdaBox
