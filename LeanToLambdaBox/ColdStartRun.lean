import LeanToLambdaBox.ColdStartInduction

/-!
# The cold-start entry point and the registration exits, decomposed (slices S3/S4)

`ErasureRun` proves the registration primitives' run shapes and `ColdStartInduction`
carries a state predicate through a whole run. Neither reaches the two ends of the
shipping pipeline:

* **the entry point** — nothing reduces `Erasure.erase e cfg` to a `visitExpr` run from
  the empty state (design item **R1**), and nothing says what `prepare_erasure` does to
  the state (**R2**);
* **the exits with their inner runs exposed** — `Erasure.run_visitMutual_ok` is stated in
  *Hoare* form over a state predicate `Q`, which is exactly right for the fixpoint
  induction and exactly wrong for the δ half: a state predicate cannot mention the
  `visitExpr` run that produced the body being stored, so it cannot carry an `Erases`
  witness for it. The δ content therefore has to be composed **outside** any induction,
  about the *real* `Erasure.visitMutual`, from a decomposition that hands the inner run
  back. `run_visitMutual_decomp` is that decomposition.

Everything here is pure `EraseM`/`CoreM` state reasoning: no `Erases`, no lean4lean, no
assumption.

## What the decomposition does and does not say

`run_visitMutual_decomp` reports the *state effect* of one `visitMutual n` call as a
three-way disjunction, one disjunct per registering exit (the fourth exit —
`@[inline]` bookkeeping — is not an exit at all: it conses to `inlinings` and falls
through, which is why it appears as the `InlineExt` slack in each disjunct rather than
as a case of its own). It deliberately does **not** decide *which* exit was taken: that
depends on `Compiler.LCNF.getDeclInfo?`, `isExtern` and `name_occurs`, i.e. on opaque
runtime data. A consumer that wants the non-recursive case discharges the other two by
`RegBridgeHyps`-class facts, or handles all three.
-/

namespace LeanToLambdaBox

open Lean Erasure

/-! ## `Kername.beq` is decidable equality

`ColdStartShape.Kername.beq_refl` is one half; the converse is what lets key
distinctness of a *later* state be read as freshness against an *earlier* lookup
(`RegDelta.mono`, slice S3). Both `ModPath.beq` and `Kername.beq` are structural. -/

theorem ModPath.eq_of_beq : ∀ {mp mp' : ModPath}, ModPath.beq mp mp' = true → mp = mp'
  | .MPfile dp, .MPfile dp', h => by simp only [ModPath.beq, beq_iff_eq] at h; rw [h]
  | .MPdot mp s, .MPdot mp' s', h => by
      simp only [ModPath.beq, Bool.and_eq_true, beq_iff_eq] at h
      rw [ModPath.eq_of_beq h.1, h.2]
  | .MPfile _, .MPdot _ _, h => by simp [ModPath.beq] at h
  | .MPdot _ _, .MPfile _, h => by simp [ModPath.beq] at h

theorem Kername.eq_of_beq {k k' : Kername} (h : Kername.beq k k' = true) : k = k' := by
  obtain ⟨mp, id⟩ := k
  obtain ⟨mp', id'⟩ := k'
  simp only [Kername.beq, Bool.and_eq_true, beq_iff_eq] at h
  rw [ModPath.eq_of_beq h.1, h.2]

theorem Kername.beq_iff {k k' : Kername} : Kername.beq k k' = true ↔ k = k' :=
  ⟨Kername.eq_of_beq, fun h => h ▸ Kername.beq_refl k⟩

/-- Key distinctness is symmetric in the sense the consumers need: a fresh key on the
left is a fresh key on the right. -/
theorem Kername.beq_false_symm {k k' : Kername} (h : Kername.beq k k' = false) :
    Kername.beq k' k = false := by
  by_contra hne
  simp only [Bool.not_eq_false] at hne
  rw [Kername.eq_of_beq hne] at h
  simp at h

/-! ## `InlineExt` — the bookkeeping slack

`visitMutual`'s inlining prefix and tail write to `ErasureState.inlinings` and to
nothing else. `Erasure.erase` returns that field *separately* from the `Program`
(`Program` is `.untyped s.gdecls (some t)`), so it is erasure-irrelevant — but the
decomposition still has to *say* so, since the post-state of a `visitMutual` call is the
registration state plus that slack. -/

/-- `s'` differs from `s` at most in `inlinings`. -/
structure InlineExt (s s' : ErasureState) : Prop where
  consts : s'.constants = s.constants
  inds : s'.inductives = s.inductives
  gdecls : s'.gdecls = s.gdecls

theorem InlineExt.rfl' (s : ErasureState) : InlineExt s s := ⟨rfl, rfl, rfl⟩

theorem InlineExt.trans {s s' s'' : ErasureState} (h : InlineExt s s')
    (h' : InlineExt s' s'') : InlineExt s s'' :=
  ⟨h'.consts.trans h.consts, h'.inds.trans h.inds, h'.gdecls.trans h.gdecls⟩

theorem InlineExt.cons (s : ErasureState) (kn : Kername) :
    InlineExt s { s with inlinings := kn :: s.inlinings } := ⟨rfl, rfl, rfl⟩

/-- An `InlineExt` is a `StateLe` (in both directions, but this is the direction the
walk needs). -/
theorem InlineExt.stateLe {s s' : ErasureState} (h : InlineExt s s') : StateLe s s' where
  consts := by rw [h.consts]; exact id
  inds := by rw [h.inds]; exact id
  gdecls := ⟨[], by simpa using h.gdecls⟩

theorem InlineExt.runConcl {s s' : ErasureState} (h : InlineExt s s') : RunConcl s s' where
  le := h.stateLe
  canon := by intro hc n k hk; rw [h.consts] at hk; exact hc hk

section Decomp

variable {n : Name} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}

/-- The inlining **tail** only conses to `inlinings`. Decomposition counterpart of
`Erasure.run_inline_tail_ok`. -/
theorem run_inline_tail_decomp {b1 b2 : Bool} {msg1 msg2 : MessageData}
    {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld}
    {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hrun : (if b1 = true then do
        let isInst ← liftM (Lean.Meta.isInstance n)
        if isInst = true then do
          logInfo msg1
          modify (fun s => { s with inlinings := toKername n :: s.inlinings })
        else if b2 = true then do
          logInfo msg2
          modify (fun s => { s with inlinings := toKername n :: s.inlinings })
        else pure ()
      else pure () : EraseM Unit) s ctx cctx ref w = .ok (u, s₁) w₁) : InlineExt s s₁ := by
  split at hrun
  · rw [Erasure.run_bind_ok] at hrun
    obtain ⟨isInst, s2, w2, hinst, hrun⟩ := hrun
    have hz := Erasure.run_liftCoreM_state (x := (Lean.Meta.isInstance n : CoreM Bool))
      _ _ cctx ref _ hinst
    subst hz
    split at hrun
    · rw [Erasure.run_bind_ok] at hrun
      obtain ⟨u3, s3, w3, hlog, hrun⟩ := hrun
      have hz2 := Erasure.run_logInfo_state _ _ cctx ref _ hlog
      subst hz2
      rw [Erasure.run_modify] at hrun
      cases hrun
      exact InlineExt.cons _ _
    · split at hrun
      · rw [Erasure.run_bind_ok] at hrun
        obtain ⟨u3, s3, w3, hlog, hrun⟩ := hrun
        have hz2 := Erasure.run_logInfo_state _ _ cctx ref _ hlog
        subst hz2
        rw [Erasure.run_modify] at hrun
        cases hrun
        exact InlineExt.cons _ _
      · rw [Erasure.run_pure] at hrun
        cases hrun
        exact InlineExt.rfl' _
  · rw [Erasure.run_pure] at hrun
    cases hrun
    exact InlineExt.rfl' _

/-- The inlining **prefix**: it conses at most one `inlinings` entry and then runs the
same continuation. Decomposition counterpart of `Erasure.run_inline_prefix_ok` — it
hands the continuation's own run back, at an `InlineExt`-shifted state. -/
theorem run_inline_prefix_decomp {b : Bool} {msg : MessageData} {rest : EraseM Unit}
    {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld}
    {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hrun : (if b = true then do
        logInfo msg
        modify (fun s => { s with inlinings := toKername n :: s.inlinings })
        rest
      else rest) s ctx cctx ref w = .ok (u, s₁) w₁) :
    ∃ (s₀ : ErasureState) (w₀ : Void IO.RealWorld) (u₀ : Unit),
      InlineExt s s₀ ∧ rest s₀ ctx cctx ref w₀ = .ok (u₀, s₁) w₁ := by
  split at hrun
  · rw [Erasure.run_bind_ok] at hrun
    obtain ⟨u1, s2, w2, hlog, hrun⟩ := hrun
    have hz := Erasure.run_logInfo_state _ _ cctx ref _ hlog
    subst hz
    rw [Erasure.run_bind_ok] at hrun
    obtain ⟨u2, s3, w3, hmod, hrun⟩ := hrun
    rw [Erasure.run_modify] at hmod
    cases hmod
    exact ⟨_, _, _, InlineExt.cons _ _, hrun⟩
  · exact ⟨_, _, _, InlineExt.rfl' _, hrun⟩

/-- **The non-recursive exit, decomposed.** The inner `visitExpr` run — the one whose
output becomes the stored constant body — is handed back, together with the exact
post-state modulo the inlining tail.

This is what the Hoare form cannot give: `Q : ErasureState → Prop` has no room for the
run, and the δ half needs it (the stored body erases *because* the bridge fires on that
run). Unlike `Erasure.run_nonrec_exit_ok` the erasure function is **not** abstract here —
the subject is the real `Erasure.visitMutual`, unfolded, so the real `Erasure.visitExpr`
is what appears. -/
theorem run_nonrec_exit_decomp {f : ErasureContext → ErasureContext} {e : Expr}
    {b1 b2 : ErasureContext → LBTerm → Bool} {msg1 msg2 : MessageData}
    {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld}
    {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hrun : (do
        let t ← withReader f (do let pe ← prepare_erasure e; visitExpr pe)
        modify (fun s => { s with
          constants := s.constants.insert n (toKername n),
          gdecls := (toKername n, .constantDecl ⟨some t⟩) :: s.gdecls })
        let c ← read
        if b1 c t = true then do
          let isInst ← liftM (Lean.Meta.isInstance n)
          if isInst = true then do
            logInfo msg1
            modify (fun s => { s with inlinings := toKername n :: s.inlinings })
          else if b2 c t = true then do
            logInfo msg2
            modify (fun s => { s with inlinings := toKername n :: s.inlinings })
          else pure ()
        else pure () : EraseM Unit) s ctx cctx ref w = .ok (u, s₁) w₁) :
    ∃ (pe : Expr) (t : LBTerm) (sp st : ErasureState) (wp wt : Void IO.RealWorld),
      prepare_erasure e s (f ctx) cctx ref w = .ok (pe, sp) wp ∧
      visitExpr pe sp (f ctx) cctx ref wp = .ok (t, st) wt ∧
      InlineExt (nonrecConstState n t st) s₁ := by
  rw [Erasure.run_bind_ok] at hrun
  obtain ⟨t, st, wt, hvis, hrun⟩ := hrun
  rw [Erasure.run_withReader, Erasure.run_bind_ok] at hvis
  obtain ⟨pe, sp, wp, hpr, hvis⟩ := hvis
  rw [Erasure.run_bind_ok] at hrun
  obtain ⟨u2, sm, wm, hmod, hrun⟩ := hrun
  rw [Erasure.run_modify] at hmod
  cases hmod
  rw [Erasure.run_bind_ok] at hrun
  obtain ⟨c2, sc, wc, hread, hrun⟩ := hrun
  rw [Erasure.run_read] at hread
  cases hread
  exact ⟨pe, t, sp, st, wp, wt, hpr, hvis, run_inline_tail_decomp hrun⟩

/-- **The recursive exit, decomposed.** The block's `gdecls` conses are pinned to
`Erasure.recConstState` at the state the per-definition erasures ended in; the
per-definition runs themselves are *not* handed back (they sit under a `List.mapM`, and
the recursive δ discharge takes them from `Erasure.erases_fix_of_open`'s own premise
list instead). -/
theorem run_rec_exit_decomp {names fixnames : List Name}
    {f : List FVarId → ErasureContext → ErasureContext}
    {g : ConstantInfo → ErasureContext → ErasureContext} {val : ConstantInfo → Expr}
    {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld}
    {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hrun : (do
        let ids ← names.mapM (fun _ => mkFreshFVarId)
        withReader (f ids) (do
          let defs ← names.mapM (fun m => do
            let ci ← getConstInfo m
            let t ← withReader (g ci) (do let pe ← prepare_erasure (val ci); visitExpr pe)
            mkDef (remove_unsafe_rec m) fixnames t)
          for p in fixnames.zipIdx do
            modify (fun s => { s with
              constants := s.constants.insert p.1 (toKername p.1),
              gdecls := (toKername p.1, .constantDecl ⟨some (.fix defs p.2)⟩) :: s.gdecls })
          pure ()) : EraseM Unit) s ctx cctx ref w = .ok (u, s₁) w₁) :
    ∃ (defs : List (@FixDef LBTerm)) (sd : ErasureState),
      s₁ = recConstState fixnames defs sd := by
  rw [Erasure.run_bind_ok] at hrun
  obtain ⟨ids, sid, wid, hids, hrun⟩ := hrun
  rw [Erasure.run_withReader, Erasure.run_bind_ok] at hrun
  obtain ⟨defs, sd, wd, hdefs, hrun⟩ := hrun
  rw [Erasure.run_bind_ok] at hrun
  obtain ⟨u4, sf, wf, hloop, hrun⟩ := hrun
  obtain ⟨hsf, -⟩ := Erasure.run_modify_forIn_ok hloop
  subst hsf
  rw [Erasure.run_pure] at hrun
  cases hrun
  exact ⟨defs, sd, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **The state effect of one `visitMutual n` call, as a disjunction over its exits.**

The three disjuncts are the three registering exits (`addAxiom`, the non-recursive
constant, the recursive block); the `@[inline]` bookkeeping is the `InlineExt` slack.
The middle disjunct hands back the inner `Erasure.visitExpr` run, which is the whole
point: it is what slice S3's δ discharge feeds to the bridge. -/
theorem run_visitMutual_decomp {s : ErasureState} {ctx : ErasureContext}
    {w : Void IO.RealWorld} {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hrun : visitMutual n s ctx cctx ref w = .ok (u, s₁) w₁) :
    (∃ s₀ : ErasureState, s₁ = addAxiomState n s₀) ∨
    (∃ (pe : Expr) (t : LBTerm) (sp st : ErasureState) (ctx' : ErasureContext)
       (wp wt : Void IO.RealWorld),
      visitExpr pe sp ctx' cctx ref wp = .ok (t, st) wt ∧
      InlineExt (nonrecConstState n t st) s₁) ∨
    (∃ (fixnames : List Name) (defs : List (@FixDef LBTerm)) (sd : ErasureState),
      s₁ = recConstState fixnames defs sd) := by
  unfold visitMutual at hrun
  simp only [] at hrun
  rw [Erasure.run_bind_ok] at hrun
  obtain ⟨di, sa, wa, hdi, hrun⟩ := hrun
  have hsa := Erasure.run_liftCoreM_state
    (x := (Compiler.LCNF.getDeclInfo? n : CoreM _)) _ _ cctx ref _ hdi
  subst hsa
  rw [Erasure.run_bind_ok] at hrun
  obtain ⟨env0, sb, wb, henv0, hrun⟩ := hrun
  have hsb := Erasure.run_getEnv_state _ _ cctx ref _ henv0
  subst hsb
  clear hdi henv0
  split at hrun
  case isTrue =>
    obtain ⟨s₀, w₀, u₀, -, hm⟩ := run_inline_prefix_decomp hrun
    rw [Erasure.run_bind_ok] at hm
    obtain ⟨env2, se, we, henv2, hm⟩ := hm
    have hz := Erasure.run_getEnv_state _ _ cctx ref _ henv2
    subst hz
    rw [Erasure.run_bind_ok] at hm
    obtain ⟨c1, sr, wr, hread, hm⟩ := hm
    rw [Erasure.run_read] at hread
    cases hread
    cases hval : di.get!.value? (allowOpaque := true) <;>
      cases hext : isExtern env2 n <;>
        cases hcfg : ctx.config.extern <;>
          simp only [hval, hext, hcfg] at hm
    all_goals
      try
        (rw [Erasure.run_bind_ok] at hm
         obtain ⟨u3, s3, w3, hlog, hm⟩ := hm
         have hz2 := Erasure.run_logInfo_state _ _ cctx ref _ hlog
         subst hz2)
    all_goals
      first
        | exact Or.inl ⟨_, (Erasure.run_addAxiom_ok hm).1⟩
        | (split at hm
           case isTrue =>
             obtain ⟨pe, t, sp, st, wp, wt, -, hvis, hext'⟩ := run_nonrec_exit_decomp hm
             exact Or.inr (Or.inl ⟨pe, t, sp, st, _, wp, wt, hvis, hext'⟩)
           case isFalse =>
             obtain ⟨defs, sd, hsd⟩ := run_rec_exit_decomp hm
             exact Or.inr (Or.inr ⟨_, defs, sd, hsd⟩))
  case isFalse =>
    split at hrun
    case isTrue =>
      obtain ⟨pe, t, sp, st, wp, wt, -, hvis, hext'⟩ := run_nonrec_exit_decomp hrun
      exact Or.inr (Or.inl ⟨pe, t, sp, st, _, wp, wt, hvis, hext'⟩)
    case isFalse =>
      obtain ⟨defs, sd, hsd⟩ := run_rec_exit_decomp hrun
      exact Or.inr (Or.inr ⟨_, defs, sd, hsd⟩)

end Decomp

/-! ## R2 — `prepare_erasure`, csimp off

`PrepareHyps` carries *four* fields: three per-transform soundness statements and their
composite `prepare_sound`, with the docstring noting the composite is "derivable … under
a monadic-bind decomposition". This is that decomposition, and `prepareSound_of_transforms`
is the derivation — so the composite field stops being an independent assumption.

Two facts come out, both needed by the entry point:

* **state transparency** — all four transforms are `CoreM` actions reached by `liftM`, so
  none of them touches the `ErasureState`. With `csimp = false` the one branch that is
  *not* a plain lift (`Core.transform` at `EraseM` through `MonadControlT`) is dead, which
  is why the gate is a premise. This is what lets the cold-start theorem run `visitExpr`
  at the **empty** state rather than at an unknown post-`prepare_erasure` state.
* **the four sub-runs**, in order, for the soundness composite. -/

section Prepare

variable {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}

/-- **R2.** With the csimp gate off, `prepare_erasure` is exactly its four
`CoreM`-lifted transforms, and it does not touch the state. -/
theorem run_prepare_erasure_ok {e : Expr} {s : ErasureState} {ctx : ErasureContext}
    {w : Void IO.RealWorld} {pe : Expr} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hcs : ctx.config.csimp = false)
    (hrun : prepare_erasure e s ctx cctx ref w = .ok (pe, s₁) w₁) :
    s₁ = s ∧ ∃ (e₁ e₂ e₃ : Expr) (v₁ v₂ v₃ : Void IO.RealWorld),
      (liftM (replaceUnsafeRecNames e) : EraseM Expr) s ctx cctx ref w = .ok (e₁, s) v₁ ∧
      (liftM (Compiler.LCNF.macroInline e₁) : EraseM Expr) s ctx cctx ref v₁
        = .ok (e₂, s) v₂ ∧
      (liftM (Compiler.LCNF.inlineMatchers e₂) : EraseM Expr) s ctx cctx ref v₂
        = .ok (e₃, s) v₃ ∧
      (liftM (Compiler.LCNF.macroInline e₃) : EraseM Expr) s ctx cctx ref v₃
        = .ok (pe, s) w₁ := by
  unfold prepare_erasure at hrun
  simp only [] at hrun
  rw [Erasure.run_bind_ok] at hrun
  obtain ⟨e₁, sa, v₁, h1, hrun⟩ := hrun
  obtain rfl := Erasure.run_liftCoreM_state _ _ cctx ref _ h1
  rw [Erasure.run_bind_ok] at hrun
  obtain ⟨e₂, sb, v₂, h2, hrun⟩ := hrun
  obtain rfl := Erasure.run_liftCoreM_state _ _ cctx ref _ h2
  rw [Erasure.run_bind_ok] at hrun
  obtain ⟨e₃, sc, v₃, h3, hrun⟩ := hrun
  obtain rfl := Erasure.run_liftCoreM_state _ _ cctx ref _ h3
  rw [Erasure.run_bind_ok] at hrun
  obtain ⟨e₄, sd, v₄, h4, hrun⟩ := hrun
  obtain rfl := Erasure.run_liftCoreM_state _ _ cctx ref _ h4
  rw [Erasure.run_read_bind] at hrun
  rw [hcs] at hrun
  simp only [Bool.false_eq_true, if_false] at hrun
  rw [Erasure.run_pure] at hrun
  cases hrun
  exact ⟨rfl, e₁, e₂, e₃, v₁, v₂, v₃, h1, h2, h3, h4⟩

/-- `prepare_erasure` does not touch the `ErasureState` — the form the entry point
consumes. -/
theorem run_prepare_erasure_state {e : Expr} {s : ErasureState} {ctx : ErasureContext}
    {w : Void IO.RealWorld} {pe : Expr} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hcs : ctx.config.csimp = false)
    (hrun : prepare_erasure e s ctx cctx ref w = .ok (pe, s₁) w₁) : s₁ = s :=
  (run_prepare_erasure_ok hcs hrun).1

/-- **`PrepareHyps`' composite is derived, not assumed.** The net evaluation-preservation
of the whole csimp-off `prepare_erasure` pipeline is the composite of its three
per-transform fields, along the decomposition R2 provides. This is why the structure
carries three fields and not four: the composite used to be a fourth, independent
trust item. -/
theorem prepare_sound_of_prepareHyps {Γ : ErasureCtx} {Esrc : SEnv}
    (HP : PrepareHyps Γ Esrc) {e pe : Expr} {s s₁ : ErasureState} {ctx : ErasureContext}
    {w w₁ : Void IO.RealWorld} (hcs : ctx.config.csimp = false)
    (hrun : prepare_erasure e s ctx cctx ref w = .ok (pe, s₁) w₁) :
    ∀ {v : Expr}, SEvalData Γ Esrc pe v ↔ SEvalData Γ Esrc e v := by
  obtain ⟨-, e₁, e₂, e₃, v₁, v₂, v₃, h1, h2, h3, h4⟩ := run_prepare_erasure_ok hcs hrun
  intro v
  exact ((HP.macroInline_sound h4).trans (HP.inlineMatchers_sound h3)).trans
    ((HP.macroInline_sound h2).trans (HP.replaceUnsafeRec_sound h1))

end Prepare

/-! ## R1 — the entry point

`Erasure.erase` is a `CoreM` computation, so stepping it needs the `CoreM`-level bind
inversion (the `EraseM` one lives one layer up). `Erasure.run` unfolds to the two
`StateT`/`ReaderT` applications by `rfl`: the initial state is the *default*
`ErasureState` and the initial context is `{ «config» := cfg }`, i.e. empty local context,
**no** fixvar map and **no** declaration universe parameters. -/

section Entry

variable {α β : Type} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
  {w : Void IO.RealWorld}

/-- Running `pure` at `CoreM`. -/
theorem core_pure (a : α) : (pure a : CoreM α) cctx ref w = .ok a w := rfl

/-- Success inversion for a `CoreM` bind. -/
theorem core_bind_ok {x : CoreM α} {f : α → CoreM β} {b : β} {w' : Void IO.RealWorld} :
    (x >>= f) cctx ref w = .ok b w' ↔
      ∃ a w₁, x cctx ref w = .ok a w₁ ∧ f a cctx ref w₁ = .ok b w' := by
  have hb : (x >>= f) cctx ref w =
      match x cctx ref w with
      | .ok a w₁ => f a cctx ref w₁
      | .error e w₁ => .error e w₁ := by
    cases hx : x cctx ref w with
    | ok a w₁ => show EST.bind (x cctx ref) _ w = _; unfold EST.bind; rw [hx]
    | error e w₁ => show EST.bind (x cctx ref) _ w = _; unfold EST.bind; rw [hx]
  rw [hb]
  cases hx : x cctx ref w with
  | ok a w₁ =>
    constructor
    · intro h; exact ⟨a, w₁, rfl, h⟩
    · rintro ⟨a', w₁', hx', hf⟩
      cases hx'
      exact hf
  | error e w₁ =>
    constructor
    · intro h; exact nomatch h
    · rintro ⟨a', w₁', hx', hf⟩
      exact nomatch hx'

/-- `Erasure.run` is the two monad-transformer applications, at the default state and
the `{ «config» := cfg }` context. -/
theorem run_eq (x : EraseM α) (cfg : ErasureConfig) :
    Erasure.run x cfg cctx ref w = x {} { «config» := cfg } cctx ref w := rfl

/-- **R1 — the cold-start entry point.** A successful `Erasure.erase e cfg` run *is* a
`prepare_erasure` run followed by a `visitExpr` run, both from the **empty** state and
under the entry context `{ «config» := cfg }`, and the returned `Program` is the final
`gdecls` paired with the erased term. Nothing is assumed. -/
theorem erase_run_ok {e : Expr} {cfg : ErasureConfig} {p : Program}
    {inls : List Kername} {w' : Void IO.RealWorld}
    (hrun : Erasure.erase e cfg cctx ref w = .ok (p, inls) w') :
    ∃ (pe : Expr) (t : LBTerm) (sp sf : ErasureState) (wp wt : Void IO.RealWorld),
      prepare_erasure e {} { «config» := cfg } cctx ref w = .ok (pe, sp) wp ∧
      visitExpr pe sp { «config» := cfg } cctx ref wp = .ok (t, sf) wt ∧
      p = .untyped sf.gdecls (some t) ∧ inls = sf.inlinings := by
  unfold Erasure.erase at hrun
  simp only [] at hrun
  rw [core_bind_ok] at hrun
  obtain ⟨ts, wt, hcore, hp⟩ := hrun
  obtain ⟨t, sf⟩ := ts
  rw [run_eq, Erasure.run_bind_ok] at hcore
  obtain ⟨pe, sp, wp, hpr, hvis⟩ := hcore
  simp only [] at hp
  rw [core_pure] at hp
  cases hp
  exact ⟨pe, t, sp, sf, wp, _, hpr, hvis, rfl, rfl⟩

end Entry

end LeanToLambdaBox
