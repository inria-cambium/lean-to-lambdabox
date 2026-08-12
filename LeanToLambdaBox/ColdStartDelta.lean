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
| `hclose` (`defs[j].body` closes `obodies[j]`) | **from the run**, as `mkDef`'s binder fold |
| the per-sibling `visitExpr` runs feeding `hopen` | **from the run** |
| `hilen`/`hnlen`/lengths | **from the run** |
| `hnd : ids.Nodup` | freshness — `BridgeHyps.fresh_run`'s business, and the loop rule here is `gw`-free by design |
| `hreg` (`Γ.recBodies` names *this* block) | **irreducible at a parameter `Γ`**: `Γ` is fixed before the run, so no run fact can say it names a block the run built. This is the run-keyed agreement that should replace `RegisteredClosureRec` |
| `hsrc`/`heclosed`/`henofv`/`hsrcfv` (the source body is a closed, fvar-free λ) | `PrepareHyps`-class facts about the prepared value |
| `hopen`'s `∀ Δf` | the same context-uniformity residue `DeltaHyps.uniform` carries |
| `hlink`, `hnest` | scoped premises, `hnest` unreachable in the intended use (see its docstring) |

So the *demotion* of `RegisteredClosureRec` to a `Γ.recBodies` agreement is unblocked but
not yet performed: the composition also needs the bridge instantiated at
`Γ.withFixvars fv` under a `BridgeInv` whose `fixvars` field agrees with the block-local
map the run installs, which is the `Γ`-inside-the-motives generalisation (design §W3.2/D8),
not something the decomposition can supply. The recursive δ witness therefore stays the
named record `EnvErasureRec.RegisteredClosureRec` for now — with a strictly smaller gap
behind it than before D6.

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
      Erases env Us Γ Δ body t → Erases env Us Γ Δ' body t) :
    RegisteredClosure env Us Γ Esrc s.gdecls where
  disj := hdisj
  erase := by
    intro n body hb
    obtain ⟨t, hmem⟩ := hreg hb
    obtain ⟨Δ, her⟩ := h.erase hb hmem
    exact ⟨t, envLookup_of_mem_of_keys hmem hkeys, fun {_} => huni hb her⟩

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
      Erases env Us Γ Δ body t → Erases env Us Γ Δ' body t)
    (hnb : ∀ {kn : Kername} {t : LBTerm},
      (kn, GlobalDecl.constantDecl ⟨some t⟩) ∈ s.gdecls → NoBlock t) :
    RegisteredClosureData env Us Γ Esrc s.gdecls where
  disj := hdisj
  erase := by
    intro n body hb
    obtain ⟨t, hmem⟩ := hreg hb
    obtain ⟨Δ, her⟩ := h.erase hb hmem
    exact ⟨t, envLookup_of_mem_of_keys hmem hkeys, fun {_} => huni hb her, hnb hmem⟩

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

/-- **Applied form of every stored body** — the one output-shape residue of the data
conversion (`hnb`). `NoBlock` is not an invariant the shape induction can carry: it proves
`NoFix`/`LBClosed` of a `visitExpr` output (`visitExpr_noFix_closed`) and not this, and
inside the bridge the erasure argument is abstract, so no motive can conclude it either. It
is therefore stated about the *environment* a run built, as a run-keyed premise of the
capstone's subject bundle — the same epistemic class as `ColdStartSubject.noBlock`, which
says the same thing about the top-level output. -/
def NoBlockEnv (E : GlobalDeclarations) : Prop :=
  ∀ {kn : Kername} {t : LBTerm}, (kn, GlobalDecl.constantDecl ⟨some t⟩) ∈ E → NoBlock t

/-- **The walk's δ record becomes the capstone's, at the walk-restricted `Esrc`** (β + δ
flavour). Compared with `registeredClosure_of_deltaMem` the existence premise `hreg` and
the key-distinctness premise `hkeys` are **gone** — `SEnv.walked`'s defining condition
supplies the first and *is* a lookup, so the second is not needed. What survives is the
context-uniformity residue `huni`, which is `DeltaHyps.uniform`. -/
theorem registeredClosure_of_deltaMem_walked {env : VEnv} {Us : List Name} {Γ : ErasureCtx}
    {Esrc : SEnv} {s : ErasureState} (h : DeltaMem env Us Γ Esrc s)
    (hdisj : ∀ {n : Name} {body : Expr}, Esrc n = some body →
      Γ.ctors n = none ∧ Γ.casesOns n = none)
    (huni : ∀ {n : Name} {body : Expr} {t : LBTerm} {Δ Δ' : VLCtx}, Esrc n = some body →
      (Γ.constants n, GlobalDecl.constantDecl ⟨some t⟩) ∈ s.gdecls →
      Erases env Us Γ Δ body t → Erases env Us Γ Δ' body t) :
    RegisteredClosure env Us Γ (Esrc.walked Γ s.gdecls) s.gdecls where
  disj := fun hb => hdisj (SEnv.walked_le hb)
  erase := by
    intro n body hb
    obtain ⟨t, hlk⟩ := SEnv.walked_lookup hb
    obtain ⟨k, hmem, hbeq⟩ := envLookup_mem hlk
    obtain rfl := Kername.eq_of_beq hbeq
    obtain ⟨Δ, her⟩ := h.erase (SEnv.walked_le hb) hmem
    exact ⟨t, hlk, fun {_} => huni (SEnv.walked_le hb) hmem her⟩

/-- **The walk's δ record becomes the capstone's, at the walk-restricted `Esrc`** (data
flavour): the same conversion, plus the applied-form conjunct the data simulation
consumes. `hnb` is the one premise `SEnv.walked` cannot retire — see `NoBlockEnv`. -/
theorem registeredClosureData_of_deltaMem_walked {env : VEnv} {Us : List Name}
    {Γ : ErasureCtx} {Esrc : SEnv} {s : ErasureState} (h : DeltaMem env Us Γ Esrc s)
    (hdisj : ∀ {n : Name} {body : Expr}, Esrc n = some body →
      Γ.ctors n = none ∧ Γ.casesOns n = none)
    (huni : ∀ {n : Name} {body : Expr} {t : LBTerm} {Δ Δ' : VLCtx}, Esrc n = some body →
      (Γ.constants n, GlobalDecl.constantDecl ⟨some t⟩) ∈ s.gdecls →
      Erases env Us Γ Δ body t → Erases env Us Γ Δ' body t)
    (hnb : NoBlockEnv s.gdecls) :
    RegisteredClosureData env Us Γ (Esrc.walked Γ s.gdecls) s.gdecls where
  disj := fun hb => hdisj (SEnv.walked_le hb)
  erase := by
    intro n body hb
    obtain ⟨t, hlk⟩ := SEnv.walked_lookup hb
    obtain ⟨k, hmem, hbeq⟩ := envLookup_mem hlk
    obtain rfl := Kername.eq_of_beq hbeq
    obtain ⟨Δ, her⟩ := h.erase (SEnv.walked_le hb) hmem
    exact ⟨t, hlk, fun {_} => huni (SEnv.walked_le hb) hmem her, hnb hmem⟩

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
    exact ⟨[], .bvar 0⟩

/-- Non-vacuity: the *later*-consed sibling does not shadow the earlier one — which is
what `envLookup_of_mem_of_keys` buys, and what a caller's `KeysDistinct` premise is for. -/
theorem gRecConstState_no_shadow :
    LBTerm.envLookup (recConstState [`f, `g] gRecDefs {}).gdecls (toKername `f)
      ≠ LBTerm.envLookup (recConstState [`f, `g] gRecDefs {}).gdecls (toKername `g) := by
  rw [gRecConstState_lookups.1, gRecConstState_lookups.2]
  simp [gRecDefs]

end LeanToLambdaBox
