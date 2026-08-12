import LeanToLambdaBox.ColdStartRun
import LeanToLambdaBox.EnvErasureRec

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
* and the bridge induction cannot host the content either — that is slice S2's recorded
  finding: its motive 6 stays `True`, because giving it content would need the abstract
  erasure argument to deliver *output shapes*, i.e. would mean merging the two 18-motive
  inductions.

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
| the recursive entry erases its source body | **scoped premise** (`RegisteredClosureRec`) — see the recursion section |
| context-uniformity (`∀ Δ`) of a constant body's erasure | **named premise** (`ErasesUniform`) — the residue `RegisteredClosure`'s own docstring already folds in |
| `Esrc`-domain ↔ walk agreement | **named premise** — `Esrc` and `Γ` are parameters |

The `∀ Δ` residue is not an oversight of this slice: `Erases` has `abstract` /
`uninstantiate` / `thin_vlet` transports, but no *weakening* over a closed subject, and
adding one is a lean4lean-side obligation (`TrExprS` weakening), not an erasure one.
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
    {Γ : ErasureCtx} {gw : Void IO.RealWorld → NameGenerator}
    (H : BridgeHyps env Us Γ gw) (HD : DataBridgeHyps Γ gw) (C : CasesBridgeHyps Γ gw)
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
  refine ⟨?_, erases_nonrec_const_body H HD C henv hvis hinv hsupp hex, hnf, hcl⟩
  rw [hpost.gdecls, hknames n]
  exact envLookup_cons_self _ _ _

/-! ## The recursive exit's registration

The δ *witness* for a recursive block is `EnvErasureRec.erases_fix_of_open`, whose premise
list is a dozen facts about the block (`closeFix` agreement, closedness and fvar-freeness
of the stored node, the `Γ.recBodies` links, the per-sibling open erasures). Producing
those from a run means reading them off the `List.mapM` over `names` that
`run_rec_exit_decomp` steps past — a per-sibling decomposition this slice does **not**
build; the recursive δ witness therefore stays the named record
`EnvErasureRec.RegisteredClosureRec`, exactly as it was.

What *is* discharged from the run is the registration half: the block really is in
`gdecls`, under the canonical kername, at the sibling's own index. -/

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

This is not a convenience: the cold-start bridge invariant's `known_dom` field forces
`known = ⊥` at the empty state (nothing is registered yet), and `Supported.const` needs
`known n`, so the cold-start fragment contains no δ-constant at all. See `ColdStart.lean`
for the full statement of that scope restriction. -/
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
        erases_nonrec_const_registered H HD C henv hknames hvis hinv hsupp hex hpost
      exact ⟨t, hlook, fun {Δ} => huni (Δ := Δ) her, hnb⟩
    · obtain ⟨body', hlook, her, hnbb⟩ := hold.erase hunf
      exact ⟨body', envLookup_mono_stateLe hle hkeys hlook, her, hnbb⟩

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

/-- Non-vacuity: the *later*-consed sibling does not shadow the earlier one — which is
what `envLookup_of_mem_of_keys` buys, and what a caller's `KeysDistinct` premise is for. -/
theorem gRecConstState_no_shadow :
    LBTerm.envLookup (recConstState [`f, `g] gRecDefs {}).gdecls (toKername `f)
      ≠ LBTerm.envLookup (recConstState [`f, `g] gRecDefs {}).gdecls (toKername `g) := by
  rw [gRecConstState_lookups.1, gRecConstState_lookups.2]
  simp [gRecDefs]

end LeanToLambdaBox
