import LeanToLambdaBox.ColdStartShape
import LeanToLambdaBox.OutputShape

/-!
# The output-shape induction over the erasure family (slices S1d, S1e)

`ColdStartShape.regInvShape_nonrec_cons_iff` shows the cold-start registry invariant
cannot get past `visitMutual`'s non-recursive constant cons without `NoFix t` and
`LBClosed t 0` of the stored `visitExpr` output — those two facts are *equivalent* to the
`nofix`/`closed` fields at that cons, so no amount of state reasoning supplies them. They
need an induction over the **results** of the 18-function erasure family ("R11").

This file is that induction, `visitExpr_shape`, run through
`Erasure.visitExpr.mutual_fixpoint_induct` with all 18 motives carrying real content.

## Shape of the statement

The induction is stated in **Hoare form** over an abstract state predicate `Q`, exactly as
`Erasure.run_visitMutual_ok` is, and for the same reason: `visitMutual` — the one member of
the family that writes to `ErasureState` — must be handled *inside* the induction, where
the step goal is about the fixpoint's abstract `visitExpr` argument rather than the real
one. `RunClosed Q` collects the six closure facts `visitMutual`'s four exits and the two
registration primitives need — none of them with a freshness side condition, see the S1e
note below; `ShapeC Q s s' t` is the per-call conclusion
"`Q` survives, and the produced term is fix-free and closed".

Two motives deviate from `ShapeC`, because their results are not λ□ terms produced from
nothing:

* motive 7 (`visitAppArgs`) additionally **takes** `NoFix`/`LBClosed` of the accumulator
  seed — the fold starts at a term the caller built (`.construct …`, a `visitConst`
  output, …), so the seed's shape is an input, not something the loop establishes;
* motive 18 (`visitAlt`) concludes `LBClosed r.2 r.1.length`, not `LBClosed r.2 0`: an
  alternative's body is closed *below its own field binders*, which is precisely the level
  `LBClosedAlts` asks for at the `.case` node that consumes it.

Motives 5/6 (`get_constant_kername`, `visitMutual`) return no term, so they conclude only
`Q s → Q s'`.

## Two matcher lemmas

`visitCases` and `visitConstructor` each dispatch on a **two-discriminant** match whose
patterns are `Name` literals. `split` cannot take those apart at a hypothesis whose subject
is the match *applied* to the monad's five arguments ("Failed to find match-expression
discriminants"), and name-pattern matchers compile to `Name.rec` + `String` `dite`s that
neither `simp` nor `rfl` reduces under a partial application. `visitCases_match_tri` and
`visitConstructor_match_quad` do the case analysis once, as a disjunction of equations
against the elaborator-generated matchers, and the induction rewrites with them. If either
shipping match is edited the matcher index moves — the failure mode is a build error, not
unsoundness.

## What comes out

* `visitExpr_noFix_closed` — **R11 with no hypotheses at all**: every successful
  `Erasure.visitExpr` run returns a fix-free, de-Bruijn-closed term. (Instantiating `Q` at
  `fun _ => True` satisfies `RunClosed` outright, so the state half evaporates and the
  shape half survives.) This is the obligation `regInvShape_nonrec_cons_iff` identified.
* `RunClosed.regInvShape` — `RegInvShape Γ` is `RunClosed`, given the registration-side
  side conditions bundled as `RegBridgeHyps`, and hence
* `visitExpr_regInvShape` / `visitMutual_regInvShape` / `get_constant_kername_regInvShape`
  — the cold-start registry invariant survives a whole `visitExpr` / `visitMutual` /
  `get_constant_kername` run.

## Slice S1e: what changed and why

S1d's version of the last three was **vacuous**: its premise record `RegShapeHyps` is
inconsistent (slice S4 refuted two fields, this slice a third). The repair was not a
weakening of that record but a change to the invariant and to one `RunClosed` field:

* `RegInvShape` trades `keys : KeysDistinct s.gdecls` for `cover : ConstKeysCovered s`.
  This is forced, not chosen: `runClosed_keysDistinct_refuted` shows **no** `RunClosed`
  predicate can contain `KeysDistinct`, because `nrc` is a bare state closure and two
  conses at one name duplicate a key.
* `RunClosed.rc` **takes** the closedness of the block being stored, which the `visitMutual`
  arm now derives per call (`rec_block_closed`) from the block shape
  `Erasure.run_rec_exit_ok` reports, instead of assuming it of an arbitrary `defs`.
* the premise record becomes `RegBridgeHyps`, merging what was left of `RegShapeHyps` with
  slice S4's own bundle, whose `regInv` field is now the theorem `visitExpr_regInvShape`.

Everything else in the 18-motive induction is S1d's, unchanged.
-/

namespace LeanToLambdaBox

open Lean Erasure

/-! ## The two name-pattern matchers -/

/-- **`visitCases`' `(typeName, config.nat)` dispatch is a trichotomy.** Stated against the
elaborator-generated matcher `Erasure.visitCases.match_7`; see the module docstring for why
`split` is unusable at the call site. -/
theorem visitCases_match_tri {α : Sort u} (nm : Name) (cn : Erasure.Config.Nat)
    (A B : Unit → α) (G : Name → Erasure.Config.Nat → α) :
    Erasure.visitCases.match_7 (motive := fun _ _ => α) nm cn A B G = A () ∨
    Erasure.visitCases.match_7 (motive := fun _ _ => α) nm cn A B G = B () ∨
    Erasure.visitCases.match_7 (motive := fun _ _ => α) nm cn A B G = G nm cn := by
  unfold Erasure.visitCases.match_7
  cases nm with
  | anonymous => exact Or.inr (Or.inr rfl)
  | num p n => exact Or.inr (Or.inr rfl)
  | str p str =>
    cases p with
    | num p2 n2 => exact Or.inr (Or.inr rfl)
    | str p2 s2 => exact Or.inr (Or.inr rfl)
    | anonymous =>
      by_cases h1 : str = "Nat"
      · subst h1
        cases cn with
        | machine => exact Or.inl rfl
        | peano => exact Or.inr (Or.inr rfl)
      · by_cases h2 : str = "Int"
        · subst h2
          cases cn with
          | machine => exact Or.inr (Or.inl rfl)
          | peano => exact Or.inr (Or.inr rfl)
        · refine Or.inr (Or.inr ?_)
          show (dite (str = "Nat") _ _) = _
          rw [dif_neg h1]
          show (dite (str = "Int") _ _) = _
          rw [dif_neg h2]

/-- **`visitConstructor`'s `(config.nat, ctorname)` dispatch is a four-way case.** The two
machine-`Nat` arms (`Nat.zero`/`Nat.succ`) are *live* here — unlike in the ι bridge, where
the supported fragment excludes them — so both are proved, not refuted. -/
theorem visitConstructor_match_quad {α : Sort u} (cn : Erasure.Config.Nat) (nm : Name)
    (A B : Unit → α) (C D : Name → α) :
    Erasure.visitConstructor.match_1 (motive := fun _ _ => α) cn nm A B C D = A () ∨
    Erasure.visitConstructor.match_1 (motive := fun _ _ => α) cn nm A B C D = B () ∨
    Erasure.visitConstructor.match_1 (motive := fun _ _ => α) cn nm A B C D = C nm ∨
    Erasure.visitConstructor.match_1 (motive := fun _ _ => α) cn nm A B C D = D nm := by
  split
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

/-! ## The interface: what a state predicate must be closed under -/

/-- **The six closure facts the shape induction needs of a state predicate.** One per place
the erasure family touches `ErasureState`:

* `inl` — `visitMutual`'s `@[inline]`/auto-inline bookkeeping exit (an `inlinings` cons);
* `ax` — `addAxiom`, in *run* form, so the panic fall-through (`addAxiom` conses a second
  entry when the constant is already registered) is covered without restating it;
* `reg` — `register_inductive`, likewise in run form: its cold branch is **not**
  state-preserving (`Erasure.run_register_inductive_cold_ok`);
* `prep` — `prepare_erasure`. The one genuinely *assumed* slot at every instantiation: its
  `csimp` branch runs `Lean.Core.transform` at `EraseM` through `MonadControlT`, so state
  transparency does not follow from the `liftM` lemmas. Epistemic class `PrepareHyps`;
* `nrc` / `rc` — `visitMutual`'s non-recursive constant cons and its recursive block cons.
  `nrc` is where the output-shape facts are consumed, which is exactly why they have to be
  proved by the same induction that uses them; `rc` is handed the block's closedness
  rather than demanding it of an arbitrary `defs` (slice S1e — see `rc`). -/
structure RunClosed (Q : ErasureState → Prop) : Prop where
  inl : ∀ {s : ErasureState} {kn : Kername},
    Q s → Q { s with inlinings := kn :: s.inlinings }
  ax : ∀ {m : Name} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
      {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {u : Unit}
      {s' : ErasureState} {w' : Void IO.RealWorld},
    addAxiom m s ctx cctx ref w = .ok (u, s') w' → Q s → Q s'
  reg : ∀ {ii : InductiveVal} {s : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
      {r : InductiveId × InductiveArgMasks} {s' : ErasureState} {w' : Void IO.RealWorld},
    register_inductive ii s ctx cctx ref w = .ok (r, s') w' → Q s → Q s'
  prep : ∀ {e : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
      {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {pe : Expr}
      {s' : ErasureState} {w' : Void IO.RealWorld},
    prepare_erasure e s ctx cctx ref w = .ok (pe, s') w' → Q s → Q s'
  nrc : ∀ {n : Name} {t : LBTerm} {s : ErasureState},
    Q s → NoFix t → LBClosed t 0 → NoBlock t → Q (nonrecConstState n t s)
  /-- The recursive block cons, **given the closedness and applied form of the block being
  stored**. Slice S1d asked for `LBClosed (.fix defs j) 0` at an arbitrary `defs`, which is
  false (`ColdStart.regShapeHyps_recClosed_refuted`). The induction now *derives* both, per
  call, from the block's own shape — `Erasure.run_rec_exit_ok` reports that each
  definition's body is a `mkDef` closure of a `visitExpr` output over the block's names, and
  `lbClosed_fix_of_bodies`/`rec_block_noBlock` do the rest. `NoBlock (.fix defs j)` is
  index-independent, so the `∀ j` there is one fact. -/
  rc : ∀ {names : List Name} {defs : List (@FixDef LBTerm)} {s : ErasureState},
    Q s → (∀ j : Nat, LBClosed (.fix defs j) 0) → (∀ j : Nat, NoBlock (.fix defs j)) →
      Q (recConstState names defs s)

/-- The per-call conclusion: from `Q` at entry, `Q` at exit **and** the produced λ□ term is
fix-free, de-Bruijn closed, and in applied form.

The third conjunct is slice δ-D7a's. It was carried as a *premise* of the two cold-start
capstones (`ColdStartSubject.noBlock`/`.noBlockEnv`) on the stated grounds that the shape
induction cannot conclude it. That was a misdiagnosis: `NoBlock` says nothing about boxing
— it forbids exactly one node, `.construct _ _ (_ :: _)` — and the eraser has exactly one
`.construct` construction site (`Erasure.visitConstructor`), nullary by explicit design
("in the stage of λbox I am targeting constructor application is function application").
So the predicate rides along as a third conjunct, and both fields retire. -/
def ShapeC (Q : ErasureState → Prop) (s s' : ErasureState) (t : LBTerm) : Prop :=
  Q s → Q s' ∧ NoFix t ∧ LBClosed t 0 ∧ NoBlock t

/-- **The recursive exit's block is closed.** The bridge between what
`Erasure.run_rec_exit_ok` hands the `rc` closure — per definition, "my body is the
`mkDef` closure of a closed erasure output over the block's names" — and what
`RegInvShape`'s `closed` field needs of the stored node. `hfix` is the shipping code's
`fixvarnames := names.map remove_unsafe_rec`, i.e. `List.length_map`. -/
theorem rec_block_closed {names fixnames : List Name} {defs : List (@FixDef LBTerm)}
    (hfix : fixnames.length = names.length) (hlen : defs.length = names.length)
    (hbodies : ∀ d ∈ defs, ∃ (t : LBTerm) (fv : Name → FVarId), LBClosed t 0 ∧
      d.body = fixnames.reverse.zipIdx.foldl (fun b p => toBvar (fv p.1) p.2 b) t)
    (j : Nat) : LBClosed (.fix defs j) 0 := by
  refine lbClosed_fix_of_bodies (k := fixnames.length) (hlen.trans hfix.symm) ?_ j
  intro d hd
  obtain ⟨t, fv, hcl, hbody⟩ := hbodies d hd
  rw [hbody]
  exact lbClosed_foldl_zipIdx_map fv fixnames hcl

/-- **The recursive exit's block is in applied form.** `rec_block_closed`'s sibling for the
third output conjunct, and strictly simpler: `NoBlock (.fix defs j)` is
`∀ d ∈ defs, NoBlock d.body` at every index, so there is no binder arithmetic — only the
`mkDef` fold, which `noBlock_foldl_zipIdx_map` discharges. -/
theorem rec_block_noBlock {fixnames : List Name} {defs : List (@FixDef LBTerm)}
    (hbodies : ∀ d ∈ defs, ∃ (t : LBTerm) (fv : Name → FVarId), NoBlock t ∧
      d.body = fixnames.reverse.zipIdx.foldl (fun b p => toBvar (fv p.1) p.2 b) t)
    (j : Nat) : NoBlock (.fix defs j) := by
  rw [NoBlock_fix]
  intro d hd
  obtain ⟨t, fv, hnb, hbody⟩ := hbodies d hd
  rw [hbody]
  exact noBlock_foldl_zipIdx_map fv fixnames hnb

/-- Split the paired per-definition report `Erasure.run_rec_exit_ok` hands the `rc` closure
— it is stated at the *abstract* output predicate `Cl`, which the induction instantiates at
`fun t => LBClosed t 0 ∧ NoBlock t` — into the shape `rec_block_closed` wants. Pure
projection; it exists so the two block-level lemmas each keep their single-fact statement.
-/
theorem rec_bodies_closed {fixnames : List Name} {defs : List (@FixDef LBTerm)}
    (h : ∀ d ∈ defs, ∃ (t : LBTerm) (fv : Name → FVarId), (LBClosed t 0 ∧ NoBlock t) ∧
      d.body = fixnames.reverse.zipIdx.foldl (fun b p => toBvar (fv p.1) p.2 b) t) :
    ∀ d ∈ defs, ∃ (t : LBTerm) (fv : Name → FVarId), LBClosed t 0 ∧
      d.body = fixnames.reverse.zipIdx.foldl (fun b p => toBvar (fv p.1) p.2 b) t :=
  fun d hd => let ⟨t, fv, hc, hb⟩ := h d hd; ⟨t, fv, hc.1, hb⟩

/-- The other half of `rec_bodies_closed`'s split, for `rec_block_noBlock`. -/
theorem rec_bodies_noBlock {fixnames : List Name} {defs : List (@FixDef LBTerm)}
    (h : ∀ d ∈ defs, ∃ (t : LBTerm) (fv : Name → FVarId), (LBClosed t 0 ∧ NoBlock t) ∧
      d.body = fixnames.reverse.zipIdx.foldl (fun b p => toBvar (fv p.1) p.2 b) t) :
    ∀ d ∈ defs, ∃ (t : LBTerm) (fv : Name → FVarId), NoBlock t ∧
      d.body = fixnames.reverse.zipIdx.foldl (fun b p => toBvar (fv p.1) p.2 b) t :=
  fun d hd => let ⟨t, fv, hc, hb⟩ := h d hd; ⟨t, fv, hc.2, hb⟩

/-! ## The induction -/

set_option maxHeartbeats 4000000 in
/-- **The output-shape induction, all 18 motives** (`R11`).

Per-motive notes on where the content sits:

* 1 `visitExpr` — the erasability gate returns `.box`; the four `unreachable!` arms return
  `default = .box`; everything else dispatches.
* 2 `visitLiteral` — the machine-`Nat` arm's 63-bit-representability `if` is split on both
  ways: the overflow branch panics, and a panic *succeeds*.
* 3 `visitConstructor` — `H.reg` for the block registration, then the four-way
  `(config.nat, ctorname)` dispatch; the `.construct` seed handed to `visitAppArgs` is
  fix-free and closed for free (no arguments are stored in the node).
* 6 `visitMutual` — `run_visitMutual_ok`'s script inlined against the *abstract* fixpoint
  argument, via the `vE`-generalized `run_nonrec_exit_ok`/`run_rec_exit_ok`.
* 7 `visitAppArgs` — `run_array_foldlM_ok`, invariant "`Q` ∧ the accumulator is fix-free and
  closed".
* 8/9/14/16 — the binder cases, closed by `toBvar`'s metatheory
  (`noFix_toBvar`, `lbClosed_toBvar`).
* 17 `visitCases` — three branches. The machine-`Nat`/`Int` arms build `.letIn`/`.case`
  nodes by hand under `withLocalDecl`; the general arm's parallel three-way `for` is driven
  by `run_array_forIn_ok` (which *accommodates* the two `Std.Stream` early exits rather than
  refuting them — the shape invariant is preserved by a `.done` that returns the
  accumulator untouched); the over-application tail is a second `forIn`.
* 18 `visitAlt` — `run_lambdaOrIntroToArity_ok`, then `run_mkAlt_ok` plus
  `lbClosed_foldl_zipIdx`, which is what pins the body's closedness level to the binder
  count. -/
theorem visitExpr_shape {Q : ErasureState → Prop} (H : RunClosed Q) :
    (∀ e s ctx cctx ref w t s' w', visitExpr e s ctx cctx ref w = .ok (t, s') w' →
      ShapeC Q s s' t) ∧
    (∀ l s ctx cctx ref w t s' w', visitLiteral l s ctx cctx ref w = .ok (t, s') w' →
      ShapeC Q s s' t) ∧
    (∀ cn args s ctx cctx ref w t s' w',
      visitConstructor cn args s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t) ∧
    (∀ e s ctx cctx ref w t s' w', visitConst e s ctx cctx ref w = .ok (t, s') w' →
      ShapeC Q s s' t) ∧
    (∀ n s ctx cctx ref w r s' w',
      get_constant_kername n s ctx cctx ref w = .ok (r, s') w' → Q s → Q s') ∧
    (∀ n s ctx cctx ref w r s' w', visitMutual n s ctx cctx ref w = .ok (r, s') w' →
      Q s → Q s') ∧
    (∀ t0 args s ctx cctx ref w t s' w',
      visitAppArgs t0 args s ctx cctx ref w = .ok (t, s') w' →
      NoFix t0 → LBClosed t0 0 → NoBlock t0 → ShapeC Q s s' t) ∧
    (∀ e s ctx cctx ref w t s' w', visitLet e s ctx cctx ref w = .ok (t, s') w' →
      ShapeC Q s s' t) ∧
    (∀ e s ctx cctx ref w t s' w', visitLambda e s ctx cctx ref w = .ok (t, s') w' →
      ShapeC Q s s' t) ∧
    (∀ tn i e s ctx cctx ref w t s' w',
      visitProj tn i e s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t) ∧
    (∀ e s ctx cctx ref w t s' w', visitApp e s ctx cctx ref w = .ok (t, s') w' →
      ShapeC Q s s' t) ∧
    (∀ e s ctx cctx ref w t s' w', visitConstApp e s ctx cctx ref w = .ok (t, s') w' →
      ShapeC Q s s' t) ∧
    (∀ cn ar e s ctx cctx ref w t s' w',
      visitCtorEta cn ar e s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t) ∧
    (∀ cn ar ty fe args s ctx cctx ref w t s' w',
      visitCtorEtaGo cn ar ty fe args s ctx cctx ref w = .ok (t, s') w' →
      ShapeC Q s s' t) ∧
    (∀ ci e s ctx cctx ref w t s' w',
      visitCasesEta ci e s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t) ∧
    (∀ ci ty fe args s ctx cctx ref w t s' w',
      visitCasesEtaGo ci ty fe args s ctx cctx ref w = .ok (t, s') w' →
      ShapeC Q s s' t) ∧
    (∀ ci args s ctx cctx ref w t s' w',
      visitCases ci args s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t) ∧
    (∀ nf mask e s ctx cctx ref w r s' w',
      visitAlt nf mask e s ctx cctx ref w = .ok (r, s') w' →
      Q s → Q s' ∧ NoFix r.2 ∧ LBClosed r.2 r.1.length ∧ NoBlock r.2) := by
  apply visitExpr.mutual_fixpoint_induct
    (motive_1 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t)
    (motive_2 := fun f => ∀ l s ctx cctx ref w t s' w',
      f l s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t)
    (motive_3 := fun f => ∀ cn args s ctx cctx ref w t s' w',
      f cn args s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t)
    (motive_4 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t)
    (motive_5 := fun f => ∀ n s ctx cctx ref w r s' w',
      f n s ctx cctx ref w = .ok (r, s') w' → Q s → Q s')
    (motive_6 := fun f => ∀ n s ctx cctx ref w r s' w',
      f n s ctx cctx ref w = .ok (r, s') w' → Q s → Q s')
    (motive_7 := fun f => ∀ t0 args s ctx cctx ref w t s' w',
      f t0 args s ctx cctx ref w = .ok (t, s') w' → NoFix t0 → LBClosed t0 0 → NoBlock t0 →
      ShapeC Q s s' t)
    (motive_8 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t)
    (motive_9 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t)
    (motive_10 := fun f => ∀ tn i e s ctx cctx ref w t s' w',
      f tn i e s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t)
    (motive_11 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t)
    (motive_12 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t)
    (motive_13 := fun f => ∀ cn ar e s ctx cctx ref w t s' w',
      f cn ar e s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t)
    (motive_14 := fun f => ∀ cn ar ty fe args s ctx cctx ref w t s' w',
      f cn ar ty fe args s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t)
    (motive_15 := fun f => ∀ ci e s ctx cctx ref w t s' w',
      f ci e s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t)
    (motive_16 := fun f => ∀ ci ty fe args s ctx cctx ref w t s' w',
      f ci ty fe args s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t)
    (motive_17 := fun f => ∀ ci args s ctx cctx ref w t s' w',
      f ci args s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t)
    (motive_18 := fun f => ∀ nf mask e s ctx cctx ref w r s' w',
      f nf mask e s ctx cctx ref w = .ok (r, s') w' →
      Q s → Q s' ∧ NoFix r.2 ∧ LBClosed r.2 r.1.length ∧ NoBlock r.2)
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₂ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₂ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₃ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₃ _
  · exact eraseM_admissible_ok₅ _
  · exact eraseM_admissible_ok₂ _
  · exact eraseM_admissible_ok₄ _
  · exact eraseM_admissible_ok₂ _
  · exact eraseM_admissible_ok₃ _
  -- Step 1: visitExpr
  · intro vE vLit vLet vLam vProj vApp ih1 ih2 ih8 ih9 ih10 ih11
    intro e s ctx cctx ref w t s' w' hrun hQ
    simp only [] at hrun
    rw [run_read_bind, run_bind_ok] at hrun
    obtain ⟨c, s₁, w₁, horc, hk⟩ := hrun
    have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ horc
    subst hs₁
    by_cases hc : c = true
    · rw [if_pos hc] at hk
      rw [run_pure] at hk
      cases hk
      exact ⟨hQ, noFix_default, lbClosed_default 0, noBlock_default⟩
    · rw [if_neg hc] at hk
      cases e <;> (try simp only [] at hk)
      case app f a => exact ih11 _ _ _ _ _ _ _ _ _ hk hQ
      case const nm us => exact ih11 _ _ _ _ _ _ _ _ _ hk hQ
      case proj tn i b => exact ih10 _ _ _ _ _ _ _ _ _ _ _ hk hQ
      case mdata d b => exact ih1 _ _ _ _ _ _ _ _ _ hk hQ
      case lam bn ty bd bi => exact ih9 _ _ _ _ _ _ _ _ _ hk hQ
      case letE bn ty v bd nd => exact ih8 _ _ _ _ _ _ _ _ _ hk hQ
      case lit l => exact ih2 _ _ _ _ _ _ _ _ _ hk hQ
      case fvar x =>
        rw [run_pure] at hk
        cases hk
        exact ⟨hQ, NoFix_fvar _, by simp, trivial⟩
      all_goals
        (rw [run_panicWithPosWithDecl] at hk
         cases hk
         exact ⟨hQ, noFix_default, lbClosed_default 0, noBlock_default⟩)
  -- Step 2: visitLiteral
  · intro vCtor ih3
    intro l s ctx cctx ref w t s' w' hrun hQ
    simp only [] at hrun
    rw [run_read_bind] at hrun
    cases hn : ctx.config.nat with
    | peano =>
      rw [hn] at hrun
      cases l with
      | natVal n =>
        cases n with
        | zero =>
          simp only [] at hrun
          exact ih3 _ _ _ _ _ _ _ _ _ _ hrun hQ
        | succ m =>
          simp only [] at hrun
          exact ih3 _ _ _ _ _ _ _ _ _ _ hrun hQ
      | strVal ss =>
        simp only [] at hrun
        rw [run_panicWithPosWithDecl] at hrun
        cases hrun
        exact ⟨hQ, noFix_default, lbClosed_default 0, noBlock_default⟩
    | machine =>
      rw [hn] at hrun
      cases l with
      | natVal n =>
        simp only [] at hrun
        split at hrun
        · rw [run_pure] at hrun
          cases hrun
          exact ⟨hQ, NoFix_prim _, by simp, trivial⟩
        · rw [run_panicWithPosWithDecl] at hrun
          cases hrun
          exact ⟨hQ, noFix_default, lbClosed_default 0, noBlock_default⟩
      | strVal ss =>
        simp only [] at hrun
        rw [run_panicWithPosWithDecl] at hrun
        cases hrun
        exact ⟨hQ, noFix_default, lbClosed_default 0, noBlock_default⟩
  -- Step 3: visitConstructor
  · intro vLit vConst vAA ih2 ih4 ih7
    intro cn args s ctx cctx ref w t s' w' hrun hQ
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨ci, s₁, w₁, hgc, hrun⟩ := hrun
    have h1 := run_getConstInfo_state _ _ cctx ref _ hgc
    subst h1
    cases ci
    case ctorInfo info =>
      simp only [] at hrun
      rw [run_bind_ok] at hrun
      obtain ⟨ci2, s₂, w₂, hgc2, hrun⟩ := hrun
      have h2 := run_getConstInfo_state _ _ cctx ref _ hgc2
      subst h2
      cases ci2
      case inductInfo indinfo =>
        simp only [] at hrun
        rw [run_bind_ok] at hrun
        obtain ⟨rr, s₃, w₃, hreg, hrun⟩ := hrun
        have hQ3 := H.reg hreg hQ
        obtain ⟨indid, argmasks⟩ := rr
        simp only [] at hrun
        rw [run_bind_ok] at hrun
        obtain ⟨env, s₄, w₄, henv, hrun⟩ := hrun
        have h4 := run_getEnv_state _ _ cctx ref _ henv
        subst h4
        rw [run_bind_ok] at hrun
        obtain ⟨c0, s₅, w₅, hrd, hrun⟩ := hrun
        rw [run_read] at hrd
        cases hrd
        split at hrun
        · exact ih7 _ _ _ _ _ _ _ _ _ _ hrun (NoFix_const _) (by simp) trivial hQ3
        · rw [run_bind_ok] at hrun
          obtain ⟨c1, s₆, w₆, hrd2, hrun⟩ := hrun
          rw [run_read] at hrd2
          cases hrd2
          rcases visitConstructor_match_quad (α := EraseM LBTerm) _ _ _ _ _ _
            with hm | hm | hm | hm <;> rw [hm] at hrun <;> (try simp only [] at hrun)
          · -- machine / Nat.zero
            split at hrun
            · exact ih2 _ _ _ _ _ _ _ _ _ hrun hQ3
            · rw [run_bind_ok] at hrun
              obtain ⟨up, s₇, w₇, hp, hrun⟩ := hrun
              rw [run_panic] at hp
              cases hp
              exact ih2 _ _ _ _ _ _ _ _ _ hrun hQ3
          · -- machine / Nat.succ
            have hsucc : ∀ {sX : ErasureState} {wX : Void IO.RealWorld},
                Q sX →
                (do let nat_add ← vConst (Expr.const ``Nat.add [])
                    vAA nat_add #[args[0]!, Expr.lit (Literal.natVal 1)] : EraseM LBTerm)
                  sX ctx cctx ref wX = .ok (t, s') w' →
                Q s' ∧ NoFix t ∧ LBClosed t 0 ∧ NoBlock t := by
              intro sX wX hQX hh
              rw [run_bind_ok] at hh
              obtain ⟨na, sY, wY, hna, hh⟩ := hh
              obtain ⟨hQY, hnfa, hcla, hnba⟩ := ih4 _ _ _ _ _ _ _ _ _ hna hQX
              exact ih7 _ _ _ _ _ _ _ _ _ _ hh hnfa hcla hnba hQY
            split at hrun
            · exact hsucc hQ3 hrun
            · rw [run_bind_ok] at hrun
              obtain ⟨up, s₇, w₇, hp, hrun⟩ := hrun
              rw [run_panic] at hp
              cases hp
              exact hsucc hQ3 hrun
          · exact ih7 _ _ _ _ _ _ _ _ _ _ hrun (NoFix_construct _ _ _) (by simp [LBClosedArgs])
              (NoBlock_construct_nil _ _) hQ3
          · exact ih7 _ _ _ _ _ _ _ _ _ _ hrun (NoFix_construct _ _ _) (by simp [LBClosedArgs])
              (NoBlock_construct_nil _ _) hQ3
      all_goals
        (simp only [] at hrun
         rw [run_panicWithPosWithDecl] at hrun
         cases hrun
         exact ⟨hQ, noFix_default, lbClosed_default 0, noBlock_default⟩)
    all_goals
      (simp only [] at hrun
       rw [run_panicWithPosWithDecl] at hrun
       cases hrun
       exact ⟨hQ, noFix_default, lbClosed_default 0, noBlock_default⟩)
  -- Step 4: visitConst
  · intro gck ih5
    intro e s ctx cctx ref w t s' w' hrun hQ
    simp only [] at hrun
    cases e <;> (try simp only [] at hrun)
    case const nm us =>
      rw [run_bind_ok] at hrun
      obtain ⟨c, s₁, w₁, hrd, hk⟩ := hrun
      rw [run_read] at hrd
      cases hrd
      cases hopt : ctx.fixvars.bind (fun hmap => hmap[nm]?) with
      | some id =>
        rw [hopt] at hk
        simp only [] at hk
        rw [run_pure] at hk
        cases hk
        exact ⟨hQ, NoFix_fvar _, by simp, trivial⟩
      | none =>
        rw [hopt] at hk
        simp only [] at hk
        rw [run_bind_ok] at hk
        obtain ⟨kn, s₂, w₂, hgck, hp⟩ := hk
        rw [run_pure] at hp
        cases hp
        exact ⟨ih5 _ _ _ _ _ _ _ _ _ hgck hQ, NoFix_const _, by simp, trivial⟩
    all_goals
      (rw [run_panicWithPosWithDecl] at hrun
       cases hrun
       exact ⟨hQ, noFix_default, lbClosed_default 0, noBlock_default⟩)
  -- Step 5: get_constant_kername
  · intro vMut ih6
    intro n s ctx cctx ref w r s' w' hrun hQ
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨s₀, s₁, w₁, hget, hk⟩ := hrun
    rw [run_get] at hget
    cases hget
    cases hcs : s.constants.get? n with
    | some kn =>
      rw [hcs] at hk
      simp only [] at hk
      rw [run_pure] at hk
      cases hk
      exact hQ
    | none =>
      rw [hcs] at hk
      simp only [] at hk
      rw [run_bind_ok] at hk
      obtain ⟨uu, s₂, w₂, hvm, hk2⟩ := hk
      rw [run_bind_ok] at hk2
      obtain ⟨s₃, s₄, w₄, hget2, hp⟩ := hk2
      rw [run_get] at hget2
      cases hget2
      rw [run_pure] at hp
      cases hp
      exact ih6 _ _ _ _ _ _ _ _ _ hvm hQ
  -- Step 6: visitMutual
  · intro vE ih1
    intro n s ctx cctx ref w u s₁ w₁ hrun hQ
    have hvE : ∀ {e' : Expr} {s' : ErasureState} {ctx' : ErasureContext}
        {w' : Void IO.RealWorld} {tt : LBTerm} {s'' : ErasureState}
        {w'' : Void IO.RealWorld},
        vE e' s' ctx' cctx ref w' = .ok (tt, s'') w'' →
        Q s' → Q s'' ∧ NoFix tt ∧ (LBClosed tt 0 ∧ NoBlock tt) :=
      fun h hq => ih1 _ _ _ _ _ _ _ _ _ h hq
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨di, sa, wa, hdi, hrun⟩ := hrun
    have hsa := run_liftCoreM_state (x := (Compiler.LCNF.getDeclInfo? n : CoreM _))
      _ _ cctx ref _ hdi
    subst hsa
    rw [run_bind_ok] at hrun
    obtain ⟨env0, sb, wb, henv0, hrun⟩ := hrun
    have hsb := run_getEnv_state _ _ cctx ref _ henv0
    subst hsb
    clear hdi henv0
    split at hrun
    case isTrue =>
      refine run_inline_prefix_ok (fun hq => H.inl hq) ?_ hQ hrun
      intro s' w' u' s'' w'' hQ' hm
      rw [run_bind_ok] at hm
      obtain ⟨env2, se, we, henv2, hm⟩ := hm
      have hz := run_getEnv_state _ _ cctx ref _ henv2
      subst hz
      rw [run_bind_ok] at hm
      obtain ⟨c1, sr, wr, hread, hm⟩ := hm
      rw [run_read] at hread
      cases hread
      cases hval : di.get!.value? (allowOpaque := true) <;>
        cases hext : isExtern env2 n <;>
          cases hcfg : ctx.config.extern <;>
            simp only [hval, hext, hcfg] at hm
      all_goals
        try
          (rw [run_bind_ok] at hm
           obtain ⟨u3, s3, w3, hlog, hm⟩ := hm
           have hz2 := run_logInfo_state _ _ cctx ref _ hlog
           subst hz2)
      all_goals
        first
          | exact H.ax hm hQ'
          | (split at hm
             case isTrue =>
               exact run_nonrec_exit_ok (Nf := NoFix) (Cl := fun tt => LBClosed tt 0 ∧ NoBlock tt)
                 (fun hq => H.inl hq) (fun h hq => H.prep h hq) hvE
                 (fun hq hnf hcl => H.nrc hq hnf hcl.1 hcl.2) hQ' hm
             case isFalse =>
               refine run_rec_exit_ok (Nf := NoFix) (Cl := fun tt => LBClosed tt 0 ∧ NoBlock tt)
                 (fun h hq => H.prep h hq) hvE ?_ hQ' hm
               intro sR defsR hqR hlenR hbodiesR
               exact H.rc hqR
                 (rec_block_closed (by simp) hlenR (rec_bodies_closed hbodiesR))
                 (rec_block_noBlock (rec_bodies_noBlock hbodiesR)))
    case isFalse =>
      split at hrun
      case isTrue =>
        exact run_nonrec_exit_ok (Nf := NoFix) (Cl := fun tt => LBClosed tt 0 ∧ NoBlock tt)
          (fun hq => H.inl hq) (fun h hq => H.prep h hq) hvE
          (fun hq hnf hcl => H.nrc hq hnf hcl.1 hcl.2) hQ hrun
      case isFalse =>
        refine run_rec_exit_ok (Nf := NoFix) (Cl := fun tt => LBClosed tt 0 ∧ NoBlock tt)
          (fun h hq => H.prep h hq) hvE ?_ hQ hrun
        intro sR defsR hqR hlenR hbodiesR
        exact H.rc hqR
          (rec_block_closed (by simp) hlenR (rec_bodies_closed hbodiesR))
          (rec_block_noBlock (rec_bodies_noBlock hbodiesR))
  -- Step 7: visitAppArgs
  · intro vE ih1
    intro t0 args s ctx cctx ref w t s' w' hrun hnf0 hcl0 hnb0 hQ
    simp only [] at hrun
    exact run_array_foldlM_ok ctx cctx ref
      (P := fun _ acc s₂ _ => Q s₂ ∧ NoFix acc ∧ LBClosed acc 0 ∧ NoBlock acc)
      ⟨hQ, hnf0, hcl0, hnb0⟩
      (fun pre x post acc s₁ w₁ acc' s₂ w₂ _ hP hg => by
        obtain ⟨hQa, hnfa, hcla, hnba⟩ := hP
        rw [run_bind_ok] at hg
        obtain ⟨u, s₃, w₃, hv, hp⟩ := hg
        rw [run_pure] at hp
        cases hp
        obtain ⟨hQ3, hnf3, hcl3, hnb3⟩ := ih1 _ _ _ _ _ _ _ _ _ hv hQa
        exact ⟨hQ3, ⟨hnfa, hnf3⟩, ⟨hcla, hcl3⟩, ⟨hnba, hnb3⟩⟩)
      hrun
  -- Step 8: visitLet
  · intro vE ih1
    intro e s ctx cctx ref w t s' w' hrun hQ
    simp only [] at hrun
    rcases run_letMonocular_ok hrun with ⟨rfl, rfl, -⟩ | ⟨x, v, b, ctx', w₀, hk⟩
    · exact ⟨hQ, noFix_default, lbClosed_default 0, noBlock_default⟩
    · rw [run_bind_ok] at hk
      obtain ⟨tv, s₁, w₁, hvv, hk2⟩ := hk
      obtain ⟨hQ1, hnfv, hclv, hnbv⟩ := ih1 _ _ _ _ _ _ _ _ _ hvv hQ
      rw [run_bind_ok] at hk2
      obtain ⟨tb, s₂, w₂, hvb, hm⟩ := hk2
      obtain ⟨hQ2, hnfb, hclb, hnbb⟩ := ih1 _ _ _ _ _ _ _ _ _ hvb hQ1
      obtain ⟨hs, hw, nm, rfl⟩ := run_mkLetIn_ok hm
      subst hs
      exact ⟨hQ2, ⟨hnfv, noFix_toBvar x 0 hnfb⟩, ⟨hclv, lbClosed_toBvar x 0 hclb⟩,
        ⟨hnbv, noBlock_toBvar x 0 hnbb⟩⟩
  -- Step 9: visitLambda
  · intro vE ih1
    intro e s ctx cctx ref w t s' w' hrun hQ
    simp only [] at hrun
    rcases run_lambdaMonocular_ok hrun with ⟨rfl, rfl, -⟩ | ⟨x, b, ctx', w₀, hk⟩
    · exact ⟨hQ, noFix_default, lbClosed_default 0, noBlock_default⟩
    · rw [run_bind_ok] at hk
      obtain ⟨tb, s₁, w₁, hvb, hm⟩ := hk
      obtain ⟨hQ1, hnfb, hclb, hnbb⟩ := ih1 _ _ _ _ _ _ _ _ _ hvb hQ
      obtain ⟨hs, hw, nm, rfl⟩ := run_mkLambda_ok hm
      subst hs
      exact ⟨hQ1, noFix_toBvar x 0 hnfb, lbClosed_toBvar x 0 hclb, noBlock_toBvar x 0 hnbb⟩
  -- Step 10: visitProj
  · intro vE ih1
    intro tn i e s ctx cctx ref w t s' w' hrun hQ
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨ci, s₁, w₁, hgc, hk⟩ := hrun
    have hs₁ := run_getConstInfo_state _ _ cctx ref _ hgc
    subst hs₁
    cases ci <;> (try simp only [] at hk)
    case inductInfo indinfo =>
      rw [run_bind_ok] at hk
      obtain ⟨rr, s₂, w₂, hreg, hk2⟩ := hk
      have hQ2 := H.reg hreg hQ
      obtain ⟨indid, argmasks⟩ := rr
      simp only [] at hk2
      rw [run_bind_ok] at hk2
      obtain ⟨te, s₃, w₃, hve, hp⟩ := hk2
      rw [run_pure] at hp
      cases hp
      obtain ⟨hQ3, -, hcl, -⟩ := ih1 _ _ _ _ _ _ _ _ _ hve hQ2
      exact ⟨hQ3, NoFix_proj _ _, hcl, trivial⟩
    all_goals
      (rw [run_panicWithPosWithDecl] at hk
       cases hk
       exact ⟨hQ, noFix_default, lbClosed_default 0, noBlock_default⟩)
  -- Step 11: visitApp
  · intro vE vAA vCA ih1 ih7 ih12
    intro e s ctx cctx ref w t s' w' hrun hQ
    simp only [] at hrun
    cases hfn : e.getAppFn
    case const cn us =>
      rw [hfn] at hrun
      simp only [] at hrun
      exact ih12 _ _ _ _ _ _ _ _ _ hrun hQ
    all_goals
      (rw [hfn] at hrun
       simp only [] at hrun
       rw [expr_withApp_eq] at hrun
       rw [run_bind_ok] at hrun
       obtain ⟨tf, s₁, w₁, hvf, hk⟩ := hrun
       obtain ⟨hQ1, hnff, hclf, hnbf⟩ := ih1 _ _ _ _ _ _ _ _ _ hvf hQ
       exact ih7 _ _ _ _ _ _ _ _ _ _ hk hnff hclf hnbf hQ1)
  -- Step 12: visitConstApp
  · intro vC vAA vCtE vCsE ih4 ih7 ih13 ih15
    intro e s ctx cctx ref w t s' w' hrun hQ
    simp only [] at hrun
    rw [expr_withApp_eq] at hrun
    cases hfn : e.getAppFn
    case const cn us =>
      rw [hfn] at hrun
      simp only [] at hrun
      rw [run_bind_ok] at hrun
      obtain ⟨o, s₁, w₁, hcs, hk⟩ := hrun
      rw [run_liftCoreM_ok] at hcs
      obtain ⟨-, rfl⟩ := hcs
      cases o with
      | some cinf =>
        simp only [] at hk
        exact ih15 _ _ _ _ _ _ _ _ _ _ hk hQ
      | none =>
        simp only [] at hk
        rw [run_bind_ok] at hk
        obtain ⟨o2, s₂, w₂, hca, hk2⟩ := hk
        rw [run_liftCoreM_ok] at hca
        obtain ⟨-, rfl⟩ := hca
        cases o2 with
        | some ar =>
          simp only [] at hk2
          exact ih13 _ _ _ _ _ _ _ _ _ _ _ hk2 hQ
        | none =>
          simp only [] at hk2
          rw [run_bind_ok] at hk2
          obtain ⟨tc, s₃, w₃, hvc, hk3⟩ := hk2
          obtain ⟨hQ3, hnfc, hclc, hnbc⟩ := ih4 _ _ _ _ _ _ _ _ _ hvc hQ
          exact ih7 _ _ _ _ _ _ _ _ _ _ hk3 hnfc hclc hnbc hQ3
    all_goals
      (rw [hfn] at hrun
       simp only [] at hrun
       rw [run_panicWithPosWithDecl] at hrun
       cases hrun
       exact ⟨hQ, noFix_default, lbClosed_default 0, noBlock_default⟩)
  -- Step 13: visitCtorEta
  · intro vCtorEtaGo ih14
    intro cn ar e s ctx cctx ref w t s' w' hrun hQ
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨type, s₁, w₁, hinfer, hk⟩ := hrun
    have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ hinfer
    subst hs₁
    rw [expr_withApp_eq] at hk
    exact ih14 _ _ _ _ _ _ _ _ _ _ _ _ _ hk hQ
  -- Step 14: visitCtorEtaGo
  · intro vConstructor vCtorEtaGo ih3 ih14
    intro cn ar ty fe args s ctx cctx ref w t s' w' hrun hQ
    simp only [] at hrun
    split at hrun
    · exact ih3 _ _ _ _ _ _ _ _ _ _ hrun hQ
    · rcases run_forallMonocular_ok hrun with ⟨rfl, rfl, -⟩ | ⟨x, bt, ctx', w₀, hk⟩
      · exact ⟨hQ, noFix_default, lbClosed_default 0, noBlock_default⟩
      · rw [run_bind_ok] at hk
        obtain ⟨res, s₁, w₁, hgo, hm⟩ := hk
        obtain ⟨hQ1, hnf, hcl, hnb⟩ := ih14 _ _ _ _ _ _ _ _ _ _ _ _ _ hgo hQ
        obtain ⟨hs, hw, nm, rfl⟩ := run_mkLambda_ok hm
        subst hs
        exact ⟨hQ1, noFix_toBvar x 0 hnf, lbClosed_toBvar x 0 hcl, noBlock_toBvar x 0 hnb⟩
  -- Step 15: visitCasesEta
  · intro vCasesEtaGo ih16
    intro cinf e s ctx cctx ref w t s' w' hrun hQ
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨type, s₁, w₁, hinfer, hk⟩ := hrun
    have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ hinfer
    subst hs₁
    rw [expr_withApp_eq] at hk
    exact ih16 _ _ _ _ _ _ _ _ _ _ _ _ hk hQ
  -- Step 16: visitCasesEtaGo
  · intro vCasesEtaGo vCases ih16 ih17
    intro cinf ty fe args s ctx cctx ref w t s' w' hrun hQ
    simp only [] at hrun
    split at hrun
    · exact ih17 _ _ _ _ _ _ _ _ _ _ hrun hQ
    · rcases run_forallMonocular_ok hrun with ⟨rfl, rfl, -⟩ | ⟨x, bt, ctx', w₀, hk⟩
      · exact ⟨hQ, noFix_default, lbClosed_default 0, noBlock_default⟩
      · rw [run_bind_ok] at hk
        obtain ⟨res, s₁, w₁, hgo, hm⟩ := hk
        obtain ⟨hQ1, hnf, hcl, hnb⟩ := ih16 _ _ _ _ _ _ _ _ _ _ _ _ hgo hQ
        obtain ⟨hs, hw, nm, rfl⟩ := run_mkLambda_ok hm
        subst hs
        exact ⟨hQ1, noFix_toBvar x 0 hnf, lbClosed_toBvar x 0 hcl, noBlock_toBvar x 0 hnb⟩
  -- Step 17: visitCases
  · intro vE vAlt ih1 ih18
    intro cinf args s ctx cctx ref w t s' w' hrun hQ
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨discr_nt, s₁, w₁, hdisc, hrun⟩ := hrun
    obtain ⟨hQ1, hnfd, hcld, hnbd⟩ := ih1 _ _ _ _ _ _ _ _ _ hdisc hQ
    rw [run_bind_ok] at hrun
    obtain ⟨c0, s₂, w₂, hrd, hrun⟩ := hrun
    rw [run_read] at hrd
    cases hrd
    rw [run_bind_ok] at hrun
    obtain ⟨ret, s₃, w₃, hmatch, htail⟩ := hrun
    have hret : Q s₃ ∧ NoFix ret ∧ LBClosed ret 0 ∧ NoBlock ret := by
      rcases visitCases_match_tri (α := EraseM LBTerm) _ _ _ _ _ with hm | hm | hm <;>
        rw [hm] at hmatch
      · -- machine `Nat`
        rw [run_bind_ok] at hmatch
        obtain ⟨zero_nt, sA, wA, hzero, hmatch⟩ := hmatch
        obtain ⟨hQA, hnfz, hclz, hnbz⟩ := ih1 _ _ _ _ _ _ _ _ _ hzero hQ1
        rw [run_bind_ok] at hmatch
        obtain ⟨bci, sB, wB, hbci, hmatch⟩ := hmatch
        have hsB := run_getConstInfo_state _ _ cctx ref _ hbci
        subst hsB
        rw [run_bind_ok] at hmatch
        obtain ⟨rr, sC, wC, hreg, hmatch⟩ := hmatch
        have hQC := H.reg hreg hQA
        obtain ⟨bool_indid, bm⟩ := rr
        simp only [] at hmatch
        obtain ⟨x, ctx', w₀, hk⟩ := run_withLocalDecl_ok hmatch
        rw [run_bind_ok] at hk
        obtain ⟨gtz_nt, sD, wD, hgtz, hk⟩ := hk
        obtain ⟨hQD, hnfg, hclg, hnbg⟩ := ih1 _ _ _ _ _ _ _ _ _ hgtz hQC
        rw [run_bind_ok] at hk
        obtain ⟨cond, sE, wE, hcond, hk⟩ := hk
        obtain ⟨hQE, hnfc, hclc, hnbc⟩ := ih1 _ _ _ _ _ _ _ _ _ hcond hQD
        rw [run_bind_ok] at hk
        obtain ⟨a1, sF, wF, ha1, hk⟩ := hk
        obtain ⟨hsF, hwF, hlen1, hb1⟩ := run_mkAlt_ok ha1
        subst hsF
        rw [run_bind_ok] at hk
        obtain ⟨a2, sG, wG, ha2, hk⟩ := hk
        obtain ⟨hsG, hwG, hlen2, hb2⟩ := run_mkAlt_ok ha2
        subst hsG
        obtain ⟨hsH, hwH, nm, rfl⟩ := run_mkLetIn_ok hk
        subst hsH
        simp only [List.length_nil, List.reverse_nil, List.zipIdx_nil,
          List.foldl_nil] at hlen1 hlen2 hb1 hb2
        refine ⟨hQE, ?_, ?_, ?_⟩
        · refine ⟨hnfd, noFix_toBvar x 0 ?_⟩
          rw [NoFix_case]
          refine ⟨hnfc, ?_⟩
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · rw [hb1]; exact hnfg
          · rw [hb2]; exact hnfz
        · refine ⟨hcld, lbClosed_toBvar x 0 ?_⟩
          rw [LBClosed_case]
          refine ⟨hclc, ?_⟩
          rw [LBClosedAlts_iff]
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · rw [hb1, hlen1]; exact hclg
          · rw [hb2, hlen2]; exact hclz
        · refine ⟨hnbd, noBlock_toBvar x 0 ?_⟩
          rw [NoBlock_case]
          refine ⟨hnbc, ?_⟩
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · rw [hb1]; exact hnbg
          · rw [hb2]; exact hnbz
      · -- machine `Int`
        rw [run_bind_ok] at hmatch
        obtain ⟨bci, sB, wB, hbci, hmatch⟩ := hmatch
        have hsB := run_getConstInfo_state _ _ cctx ref _ hbci
        subst hsB
        rw [run_bind_ok] at hmatch
        obtain ⟨rr, sC, wC, hreg, hmatch⟩ := hmatch
        have hQC := H.reg hreg hQ1
        obtain ⟨bool_indid, bm⟩ := rr
        simp only [] at hmatch
        obtain ⟨x, ctx', w₀, hk⟩ := run_withLocalDecl_ok hmatch
        rw [run_bind_ok] at hk
        obtain ⟨ofn, sD, wD, hofn, hk⟩ := hk
        obtain ⟨hQD, hnfo, hclo, hnbo⟩ := ih1 _ _ _ _ _ _ _ _ _ hofn hQC
        rw [run_bind_ok] at hk
        obtain ⟨neg, sE, wE, hneg, hk⟩ := hk
        obtain ⟨hQE, hnfn, hcln, hnbn⟩ := ih1 _ _ _ _ _ _ _ _ _ hneg hQD
        rw [run_bind_ok] at hk
        obtain ⟨ineg, sF, wF, hineg, hk⟩ := hk
        obtain ⟨hQF, hnfin, hclin, hnbin⟩ := ih1 _ _ _ _ _ _ _ _ _ hineg hQE
        rw [run_bind_ok] at hk
        obtain ⟨nsucc, sG, wG, hnsucc, hk⟩ := hk
        obtain ⟨hQG, hnfs, hcls, hnbs⟩ := ih1 _ _ _ _ _ _ _ _ _ hnsucc hQF
        rw [run_bind_ok] at hk
        obtain ⟨cond, sH, wH, hcond, hk⟩ := hk
        obtain ⟨hQH, hnfc, hclc, hnbc⟩ := ih1 _ _ _ _ _ _ _ _ _ hcond hQG
        rw [run_bind_ok] at hk
        obtain ⟨a1, sI, wI, ha1, hk⟩ := hk
        obtain ⟨hsI, hwI, hlen1, hb1⟩ := run_mkAlt_ok ha1
        subst hsI
        rw [run_bind_ok] at hk
        obtain ⟨a2, sJ, wJ, ha2, hk⟩ := hk
        obtain ⟨hsJ, hwJ, hlen2, hb2⟩ := run_mkAlt_ok ha2
        subst hsJ
        obtain ⟨hsK, hwK, nm, rfl⟩ := run_mkLetIn_ok hk
        subst hsK
        simp only [List.length_nil, List.reverse_nil, List.zipIdx_nil,
          List.foldl_nil] at hlen1 hlen2 hb1 hb2
        refine ⟨hQH, ?_, ?_, ?_⟩
        · refine ⟨hnfd, noFix_toBvar x 0 ?_⟩
          rw [NoFix_case]
          refine ⟨hnfc, ?_⟩
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · rw [hb1]; exact ⟨hnfn, hnfin, hnfs, NoFix_fvar _⟩
          · rw [hb2]; exact ⟨hnfo, NoFix_fvar _⟩
        · refine ⟨hcld, lbClosed_toBvar x 0 ?_⟩
          rw [LBClosed_case]
          refine ⟨hclc, ?_⟩
          rw [LBClosedAlts_iff]
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · rw [hb1, hlen1]; exact ⟨hcln, hclin, hcls, trivial⟩
          · rw [hb2, hlen2]; exact ⟨hclo, trivial⟩
        · refine ⟨hnbd, noBlock_toBvar x 0 ?_⟩
          rw [NoBlock_case]
          refine ⟨hnbc, ?_⟩
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · rw [hb1]; exact ⟨hnbn, hnbin, hnbs, trivial⟩
          · rw [hb2]; exact ⟨hnbo, trivial⟩
      · -- the general arm
        rw [run_bind_ok] at hmatch
        obtain ⟨cinfo, sA, wA, hgci, hmatch⟩ := hmatch
        have hsA := run_getConstInfo_state _ _ cctx ref _ hgci
        subst hsA
        cases cinfo <;> (try simp only [] at hmatch)
        case inductInfo indVal =>
          rw [run_bind_ok] at hmatch
          obtain ⟨rr, sB, wB, hreg, hmatch⟩ := hmatch
          have hQB := H.reg hreg hQ1
          obtain ⟨indid, argmasks⟩ := rr
          simp only [] at hmatch
          rw [run_bind_ok] at hmatch
          obtain ⟨accfin, sC, wC, hloop, hp⟩ := hmatch
          rw [run_pure] at hp
          cases hp
          have hloopP := run_array_forIn_ok ctx cctx ref
            (P := fun acc sX (_ : Void IO.RealWorld) =>
              Q sX ∧ ∀ a ∈ acc.1, NoFix a.2 ∧ LBClosed a.2 a.1.length ∧ NoBlock a.2)
            _ _ _ _ _
            ⟨hQB, by intro a ha; simp at ha⟩
            (fun i _ acc sX wX st sY wY hP hb => by
              obtain ⟨hQX, hall⟩ := hP
              obtain ⟨alts, sAlt, sMask⟩ := acc
              simp only [] at hb hall ⊢
              cases hna : Std.Stream.next? sMask with
              | none =>
                rw [hna] at hb
                simp only [] at hb
                rw [run_pure] at hb
                cases hb
                exact ⟨hQX, hall⟩
              | some p =>
                obtain ⟨argmask, sMask'⟩ := p
                rw [hna] at hb
                simp only [] at hb
                cases hna2 : Std.Stream.next? sAlt with
                | none =>
                  rw [hna2] at hb
                  simp only [] at hb
                  rw [run_pure] at hb
                  cases hb
                  exact ⟨hQX, hall⟩
                | some p2 =>
                  obtain ⟨altInfo, sAlt'⟩ := p2
                  rw [hna2] at hb
                  simp only [] at hb
                  rw [run_bind_ok] at hb
                  obtain ⟨alt, sZ, wZ, halt, hp2⟩ := hb
                  obtain ⟨hQZ, hnfa, hcla, hnba⟩ := ih18 _ _ _ _ _ _ _ _ _ _ _ halt hQX
                  rw [run_pure] at hp2
                  cases hp2
                  refine ⟨hQZ, ?_⟩
                  intro a ha
                  rcases Array.mem_or_eq_of_mem_push ha with ha | rfl
                  · exact hall a ha
                  · exact ⟨hnfa, hcla, hnba⟩)
            _ _ _ hloop
          obtain ⟨hQfin, hallfin⟩ := hloopP
          refine ⟨hQfin, ?_, ?_, ?_⟩
          · rw [NoFix_case]
            refine ⟨hnfd, ?_⟩
            intro a ha
            exact (hallfin a (Array.mem_toList_iff.mp ha)).1
          · rw [LBClosed_case]
            refine ⟨hcld, ?_⟩
            rw [LBClosedAlts_iff]
            intro a ha
            rw [Nat.zero_add]
            exact (hallfin a (Array.mem_toList_iff.mp ha)).2.1
          · rw [NoBlock_case]
            refine ⟨hnbd, ?_⟩
            intro a ha
            exact (hallfin a (Array.mem_toList_iff.mp ha)).2.2
        all_goals
          (rw [run_panicWithPosWithDecl] at hmatch
           cases hmatch
           exact ⟨hQ1, noFix_default, lbClosed_default 0, noBlock_default⟩)
    obtain ⟨hQ3, hnfr, hclr, hnbr⟩ := hret
    rw [run_bind_ok] at htail
    obtain ⟨tfin, s₄, w₄, hloop2, hp2⟩ := htail
    rw [run_pure] at hp2
    cases hp2
    exact run_array_forIn_ok ctx cctx ref
      (P := fun acc sX (_ : Void IO.RealWorld) => Q sX ∧ NoFix acc ∧ LBClosed acc 0 ∧ NoBlock acc)
      _ _ _ _ _ ⟨hQ3, hnfr, hclr, hnbr⟩
      (fun a _ acc sX wX st sY wY hP hb => by
        obtain ⟨hQX, hnfa, hcla, hnba⟩ := hP
        rw [run_bind_ok] at hb
        obtain ⟨tx, sZ, wZ, hvx, hp3⟩ := hb
        rw [run_pure] at hp3
        cases hp3
        obtain ⟨hQZ, hnfx, hclx, hnbx⟩ := ih1 _ _ _ _ _ _ _ _ _ hvx hQX
        exact ⟨hQZ, ⟨hnfa, hnfx⟩, ⟨hcla, hclx⟩, ⟨hnba, hnbx⟩⟩)
      _ _ _ hloop2
  -- Step 18: visitAlt
  · intro vE ih1
    intro nf mask e s ctx cctx ref w r s' w' hrun hQ
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨ty, s₁, w₁, hinfer, hk⟩ := hrun
    have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ hinfer
    subst hs₁
    rcases run_lambdaOrIntroToArity_ok nf hk with ⟨rfl, rfl⟩ | ⟨e', xs, ctx', w₀, hlen, hK⟩
    · exact ⟨hQ, trivial, trivial, trivial⟩
    · rw [run_bind_ok] at hK
      obtain ⟨tb, s₂, w₂, hvb, hm⟩ := hK
      obtain ⟨hQ2, hnfb, hclb, hnbb⟩ := ih1 _ _ _ _ _ _ _ _ _ hvb hQ
      obtain ⟨hs, hw, hlen2, hbody⟩ := run_mkAlt_ok hm
      subst hs
      refine ⟨hQ2, ?_, ?_, ?_⟩
      · rw [hbody]; exact noFix_foldl_toBvar _ hnfb
      · rw [hbody, hlen2]; exact lbClosed_foldl_zipIdx _ hclb
      · rw [hbody]; exact noBlock_foldl_toBvar _ hnbb

/-! ## R11, unconditionally

`RunClosed` is satisfied outright at the trivial predicate — every field's conclusion is
`True` — so instantiating the induction there discards the state half and leaves the output
half standing with **no hypotheses**. That is R11 in its strongest form, and simultaneously
the non-vacuity guard for `RunClosed`: the class is inhabited, so `visitExpr_shape` cannot
be true merely because its premise is unsatisfiable. -/

/-- Non-vacuity: the trivial predicate is `RunClosed`. -/
theorem runClosed_true : RunClosed (fun _ => True) where
  inl := fun _ => trivial
  ax := fun _ _ => trivial
  reg := fun _ _ => trivial
  prep := fun _ _ => trivial
  nrc := fun _ _ _ _ => trivial
  rc := fun _ _ _ => trivial

/-- **R11, in full.** Every successful run of the shipping `Erasure.visitExpr` returns a
term that contains no `.fix`, has no loose de Bruijn index, and is in applied form. No
hypotheses: not on the state, not on the source expression, not on the configuration.

The third conjunct is slice δ-D7a's; see `ShapeC`. -/
theorem visitExpr_shape_all {e : Expr} {s : ErasureState} {ctx : ErasureContext}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {t : LBTerm} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : visitExpr e s ctx cctx ref w = .ok (t, s') w') :
    NoFix t ∧ LBClosed t 0 ∧ NoBlock t :=
  ((visitExpr_shape runClosed_true).1 _ _ _ _ _ _ _ _ _ hrun trivial).2

/-- **R11.** The two conjuncts the registry argument asks for, as a thin wrapper on
`visitExpr_shape_all` — kept under its own name because it is what
`regInvShape_nonrec_cons_iff` identified as the cold-start invariant's obligation at
`visitMutual`'s non-recursive constant cons, and what every downstream site names. -/
theorem visitExpr_noFix_closed {e : Expr} {s : ErasureState} {ctx : ErasureContext}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {t : LBTerm} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : visitExpr e s ctx cctx ref w = .ok (t, s') w') :
    NoFix t ∧ LBClosed t 0 :=
  let h := visitExpr_shape_all hrun
  ⟨h.1, h.2.1⟩

/-- **Applied form of every `visitExpr` output**, on its own — the fact that used to be
`ColdStartSubject.noBlock`, a premise of both cold-start capstones. -/
theorem visitExpr_noBlock {e : Expr} {s : ErasureState} {ctx : ErasureContext}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {t : LBTerm} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : visitExpr e s ctx cctx ref w = .ok (t, s') w') : NoBlock t :=
  (visitExpr_shape_all hrun).2.2

/-- The `Q`-generic form: the output-shape half of the induction at an arbitrary
`RunClosed` predicate. -/
theorem visitExpr_output_shape {Q : ErasureState → Prop} (H : RunClosed Q) {e : Expr}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {t : LBTerm}
    {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : visitExpr e s ctx cctx ref w = .ok (t, s') w') (hQ : Q s) :
    Q s' ∧ NoFix t ∧ LBClosed t 0 ∧ NoBlock t :=
  (visitExpr_shape H).1 _ _ _ _ _ _ _ _ _ hrun hQ

/-! ## `RegInvShape` is `RunClosed`

The instantiation the cold-start argument actually wants, and the slice that repairs it.

### What slice S1d got wrong, and how far

S1d collected the registration-side side conditions in `RegShapeHyps` (kept below as a
negative guard) and derived `RunClosed (RegInvShape Γ)` from them. Slice S4 refuted two of
its fields; this slice found the defect is deeper than the record. With S1's `keys :
KeysDistinct s.gdecls` field in the invariant, **`RunClosed (RegInvShape Γ)` is itself
false** — `runClosed_keysDistinct_refuted` below proves it, from `nrc` alone, which is a
bare state closure with no run and hence no side condition that could rescue it. No repair
of the hypotheses was available; the invariant had to change.

### The repaired premise set

`RegInvShape` now carries `cover : ConstKeysCovered s` in place of `keys`, and every
environment-plumbing obligation is *proved*:

* `inl`, `ax`, `nrc`, `rc` — `ColdStartShape`'s closure lemmas, now with **no** freshness
  side condition at all (the block records are scoped to `BlockRegistered s.gdecls`, which
  a `.constantDecl` cons cannot forge, and coverage is preserved outright);
* `rc` additionally needs the stored block to be closed, which the induction derives per
  call from `Erasure.run_rec_exit_ok`'s report of the block's shape (`rec_block_closed`) —
  S1d's `recClosed`, refuted at `.fix [{body := .bvar 5}] 0`, is gone;
* `reg` — the hit branch is state-preserving and needs nothing; the cold branch needs the
  `Γ`-agreement for the block it just registered, which is a parameter-side obligation and
  stays in the bundle, now **guarded by the cold branch's own test**
  (`s.inductives.get? ii.name = none`). That guard is what makes the field consistent: the
  *hit* run is constructible in-logic (`run_get`/`run_pure` plus an arbitrary world token),
  and S1d's unguarded fields were refutable through it at every `Γ` that records a
  constructor at all. A cold run is not constructible — its body reads the environment
  through `getConstInfo` — so the guarded field sits in the epistemic class of
  `BridgeHyps`.
* `prep` — the `PrepareHyps`-class transparency of `prepare_erasure`, unchanged.

### Scope: what a hostile `Γ` can still do

`Γ` is a *parameter*, and the invariant's `ctors`/`cases`/`fields` are its specification.
A `Γ` that records a constructor for a block the walk registers *empty* falsifies the
invariant at the post-state, hence falsifies the bundle: with `ii.all = []` the cold branch
degenerates to a constructible run that conses `.inductiveDecl ⟨_, []⟩` under
`rootKername ""`. Nothing here can prevent that, and nothing should: it is the operational
meaning of "`Γ` is the specification of the registration". Every `Γ` describing a real Lean
environment is clear of it. -/

/-- **The registration bundle, repaired (slice S1e).** The obligations of a cold-start
registration argument that are *not* derivable, in one record: the naming convention, the
`Γ`-agreement for a freshly registered block, the `prepare_erasure` trust item, and the
completeness ("saturation") facts the capstone needs to collapse the scoped records.

This is the single interface — it replaces both `RegShapeHyps` (refuted) and slice S4's
`RegBridgeHyps`, whose `regInv` field is now the theorem `visitExpr_regInvShape`. -/
structure RegBridgeHyps (Γ : ErasureCtx) : Prop where
  /-- `hknames`: `Γ` files every constant under its canonical kername. A side condition on
  the parameter `Γ`, `rfl` at every concrete one in this repo. -/
  knames : ∀ n : Name, Γ.constants n = toKername n
  /-- `Γ`-agreement for the constructors of a block a **cold** `register_inductive` has
  just registered. -/
  regCtors : ∀ {ii : InductiveVal} {s : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
      {r : InductiveId × InductiveArgMasks} {s' : ErasureState} {w' : Void IO.RealWorld},
    s.inductives.get? ii.name = none →
    register_inductive ii s ctx cctx ref w = .ok (r, s') w' →
    ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
      Kername.beq (mutualBlockKn ii) iid.mutualBlockName = true →
      Γ.ctors cn = some (iid, cidx) → RegisteredCtor Γ s'.gdecls cn iid cidx
  /-- `Γ`-agreement for the `casesOn` data of that block. -/
  regCases : ∀ {ii : InductiveVal} {s : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
      {r : InductiveId × InductiveArgMasks} {s' : ErasureState} {w' : Void IO.RealWorld},
    s.inductives.get? ii.name = none →
    register_inductive ii s ctx cctx ref w = .ok (r, s') w' →
    ∀ {con : Name} {iid : InductiveId} {np : Nat},
      Kername.beq (mutualBlockKn ii) iid.mutualBlockName = true →
      Γ.casesOns con = some (iid, np) →
      ∃ (body : MutualInductiveBody) (oib : OneInductiveBody),
        LBTerm.envLookup s'.gdecls iid.mutualBlockName = some (.inductiveDecl body) ∧
        body.bodies[iid.idx]? = some oib ∧ body.npars = np ∧ oib.propositional = false
  /-- `Γ`-agreement for the field counts of that block. -/
  regFields : ∀ {ii : InductiveVal} {s : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
      {r : InductiveId × InductiveArgMasks} {s' : ErasureState} {w' : Void IO.RealWorld},
    s.inductives.get? ii.name = none →
    register_inductive ii s ctx cctx ref w = .ok (r, s') w' →
    ∀ {con : Name} {iid : InductiveId} {np : Nat},
      Kername.beq (mutualBlockKn ii) iid.mutualBlockName = true →
      Γ.casesOns con = some (iid, np) → RegisteredCtorFields Γ s'.gdecls iid
  /-- `PrepareHyps`-class: `prepare_erasure` does not disturb the registry invariant. Its
  `csimp` branch runs `Lean.Core.transform` at `EraseM` through `MonadControlT`, so state
  transparency does not follow from the `liftM` lemmas. -/
  prep : ∀ {e : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
      {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {pe : Expr}
      {s' : ErasureState} {w' : Void IO.RealWorld},
    prepare_erasure e s ctx cctx ref w = .ok (pe, s') w' → RegInvShape Γ s → RegInvShape Γ s'
  /-- **Completeness.** Every inductive block `Γ` records a constructor for was registered
  by the walk. `RegInvShape`'s registration records are scoped to
  `BlockRegistered s.gdecls` precisely because a partial run has registered only part of
  `Γ`; collapsing them to the unscoped records the capstones consume needs exactly this,
  and `Γ` being a parameter, nothing about the run can supply it. -/
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

/-- **`RegInvShape Γ` is `RunClosed`.** Five of the six fields are discharged from
`ColdStartShape`'s closure lemmas — including `reg`'s hit branch, which is
state-preserving; what the bundle supplies is the `Γ`-agreement for a cold registration
and the `prepare_erasure` trust item. -/
theorem RunClosed.regInvShape {Γ : ErasureCtx} (Hg : RegBridgeHyps Γ) :
    RunClosed (RegInvShape Γ) where
  inl := fun h => h.inlinings
  ax := fun hrun hQ => (hQ.addAxiom_run (Hg.knames _) hrun).1
  reg := by
    intro ii s ctx cctx ref w r s' w' hrun hQ
    cases hi : s.inductives.get? ii.name with
    | some rc0 =>
      obtain ⟨-, hs, -⟩ := run_register_inductive_hit_ok hi hrun
      subst hs
      exact hQ
    | none =>
      exact (hQ.register_inductive_run Hg.knames (Hg.regCtors hi hrun)
        (Hg.regCases hi hrun) (Hg.regFields hi hrun) hrun).1
  prep := fun hrun hQ => Hg.prep hrun hQ
  nrc := fun hQ hnf hcl _ => hQ.nonrecConst (Hg.knames _) hnf hcl
  rc := fun hQ hcl _ => RegInvShape.recConst Hg.knames hcl hQ

/-- **The registry invariant survives a whole `visitExpr` run** — and the output it
produces is a legal constant body. This is slice S4's `RegBridgeHyps.regInv` field,
now a theorem. -/
theorem visitExpr_regInvShape {Γ : ErasureCtx} (Hg : RegBridgeHyps Γ) {e : Expr}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {t : LBTerm}
    {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : visitExpr e s ctx cctx ref w = .ok (t, s') w') (h : RegInvShape Γ s) :
    RegInvShape Γ s' ∧ NoFix t ∧ LBClosed t 0 ∧ NoBlock t :=
  visitExpr_output_shape (RunClosed.regInvShape Hg) hrun h

/-- **The registry invariant survives a whole `visitMutual` run** — the DAG walk that
registers a Lean mutual block and everything it transitively depends on. -/
theorem visitMutual_regInvShape {Γ : ErasureCtx} (Hg : RegBridgeHyps Γ) {n : Name}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {u : Unit}
    {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : visitMutual n s ctx cctx ref w = .ok (u, s') w') (h : RegInvShape Γ s) :
    RegInvShape Γ s' :=
  (visitExpr_shape (RunClosed.regInvShape Hg)).2.2.2.2.2.1 _ _ _ _ _ _ _ _ _ hrun h

/-- Same, for `get_constant_kername` — the memoized entry point the constant cases go
through. -/
theorem get_constant_kername_regInvShape {Γ : ErasureCtx} (Hg : RegBridgeHyps Γ) {n : Name}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {kn : Kername}
    {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : get_constant_kername n s ctx cctx ref w = .ok (kn, s') w') (h : RegInvShape Γ s) :
    RegInvShape Γ s' :=
  (visitExpr_shape (RunClosed.regInvShape Hg)).2.2.2.2.1 _ _ _ _ _ _ _ _ _ hrun h

/-! ## Guards

### The negative guard: why the invariant lost its `keys` field

Not a design preference — a theorem. `RunClosed.nrc` is a *state* closure: it is applied
inside `Erasure.run_nonrec_exit_ok` at whatever state the constant body's erasure left
behind, with no run in scope and hence nothing to condition on. So a predicate that
contains `KeysDistinct s.gdecls` must be closed under `nonrecConstState n t ·` at every
state it admits — including the state a first such cons produces, where the second cons
duplicates the key. -/

/-- **Key distinctness cannot ride along the shape induction.** At **no** `Γ` — no side
condition, no naming assumption — can a `RunClosed` predicate carry `KeysDistinct` of
`gdecls`. Two `nrc` steps at the same name are all it takes.

This subsumes slice S4's two refutations of `RegShapeHyps` as an explanation: those
identified fields that were false, this identifies the field of the *invariant* that made
`RunClosed (RegInvShape Γ)` unprovable no matter which hypotheses were bundled with it. -/
theorem runClosed_keysDistinct_refuted {Γ : ErasureCtx}
    (H : RunClosed (fun s => RegInvShape Γ s ∧ KeysDistinct s.gdecls)) : False := by
  have h0 : RegInvShape Γ {} ∧ KeysDistinct ({} : ErasureState).gdecls :=
    ⟨RegInvShape.empty Γ, KeysDistinct.nil⟩
  have h1 := H.nrc (n := `x) (t := .box) h0 (by simp [NoFix]) (by simp [LBClosed]) trivial
  have h2 := H.nrc (n := `x) (t := .box) h1 (by simp [NoFix]) (by simp [LBClosed]) trivial
  have := (List.pairwise_cons.mp h2.2).1 (toKername `x, .constantDecl ⟨some .box⟩)
    List.mem_cons_self
  simp at this

/-! ### The positive guard

The bundle is inhabited, at a concrete `Γ` and with every field that *can* be discharged
discharged. `prep` is the one residue, and it is hypothetical for the reason its docstring
gives — it is the same trust item slice S1d carried, and the same one `RunClosed.prep`
names at every instantiation.

What the guard shows that S1d's could not: the record is **consistent**. Its registration
fields are vacuous at this `Γ` (which records no constructor), but they are no longer
*refutable* at a `Γ` that records one, because the cold guard has removed the hit-branch
instantiation that made S1d's versions false — see the section docstring. -/

/-- A concrete `Γ` filing every constant under its canonical kername. -/
private def gΓrb : ErasureCtx where
  inductives := fun _ => none
  constants := toKername
  ctors := fun _ => none
  ctorArities := fun _ => none
  casesOns := fun _ => none

/-- Non-vacuity: the repaired bundle is inhabited, modulo the one documented trust item. -/
theorem gRegBridgeHyps
    (hprep : ∀ {e : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
      {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {pe : Expr}
      {s' : ErasureState} {w' : Void IO.RealWorld},
      prepare_erasure e s ctx cctx ref w = .ok (pe, s') w' →
      RegInvShape gΓrb s → RegInvShape gΓrb s') :
    RegBridgeHyps gΓrb where
  knames := fun _ => rfl
  regCtors := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc; exact absurd hc (by simp [gΓrb])
  regCases := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc; exact absurd hc (by simp [gΓrb])
  regFields := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc; exact absurd hc (by simp [gΓrb])
  prep := hprep
  satCtors := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ hc; exact absurd hc (by simp [gΓrb])
  satCases := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ hc; exact absurd hc (by simp [gΓrb])

/-- …and the corollaries fire on it: the registry invariant really is carried through a
`visitExpr` run by the repaired bundle, not vacuously. (The run itself stays hypothetical
— no run of the erasure family is constructible in-logic.) -/
theorem gVisitExpr_regInvShape
    (hprep : ∀ {e : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
      {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {pe : Expr}
      {s' : ErasureState} {w' : Void IO.RealWorld},
      prepare_erasure e s ctx cctx ref w = .ok (pe, s') w' →
      RegInvShape gΓrb s → RegInvShape gΓrb s')
    {e : Expr} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {t : LBTerm}
    {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : visitExpr e {} ctx cctx ref w = .ok (t, s') w') :
    RegInvShape gΓrb s' ∧ NoFix t ∧ LBClosed t 0 ∧ NoBlock t :=
  visitExpr_regInvShape (gRegBridgeHyps hprep) hrun (RegInvShape.empty gΓrb)

/-! ## The superseded record

`RegShapeHyps` is slice S1d's version of the bundle above. It is **inconsistent** —
`ColdStart.regShapeHyps_fresh_refuted` and `ColdStart.regShapeHyps_recClosed_refuted`
prove it two independent ways — and it is kept, unused, as the negative guard those
refutations are about: the repo's standing rule is that a refuted statement stays with its
refutation, so that the record of *why* an interface changed is machine-checked rather
than narrated.

Its defects, one line each:

* `fresh`/`recKeys` — freshness quantified over every state the invariant admits, with
  nothing tying it to the call. Refuted. The deeper problem was the `keys` field they were
  serving: `runClosed_keysDistinct_refuted`.
* `regKeys`/`regCtors`/`regCases`/`regFields` — no cold guard, so the constructible *hit*
  run instantiates them at a hand-made state with empty `gdecls`.
* `recClosed` — `LBClosed (.fix defs j) 0` for every `defs`. Refuted at `.bvar 5`.
* `knames`/`prep` — sound; they survive into `RegBridgeHyps`. -/

/-- The registration-side side conditions of the cold-start shape argument as slice S1d
stated them. **Inconsistent** — see the section docstring and the two refutations in
`ColdStart.lean`. Superseded by `RegBridgeHyps`; kept as a negative guard, and not used by
anything. -/
structure RegShapeHyps (Γ : ErasureCtx) : Prop where
  /-- `hknames`: `Γ` files every constant under its canonical kername. -/
  knames : ∀ n : Name, Γ.constants n = toKername n
  /-- Key freshness at every constant cons (`addAxiom` and the non-recursive exit). -/
  fresh : ∀ {n : Name} {s : ErasureState}, RegInvShape Γ s →
    ∀ p ∈ s.gdecls, Kername.beq (toKername n) p.1 = false
  /-- Key distinctness of the post-`register_inductive` environment. -/
  regKeys : ∀ {ii : InductiveVal} {s : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
      {r : InductiveId × InductiveArgMasks} {s' : ErasureState} {w' : Void IO.RealWorld},
    register_inductive ii s ctx cctx ref w = .ok (r, s') w' → KeysDistinct s'.gdecls
  /-- `Γ`-agreement for the constructors of the block just registered. -/
  regCtors : ∀ {ii : InductiveVal} {s : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
      {r : InductiveId × InductiveArgMasks} {s' : ErasureState} {w' : Void IO.RealWorld},
    register_inductive ii s ctx cctx ref w = .ok (r, s') w' →
    ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
      Kername.beq (mutualBlockKn ii) iid.mutualBlockName = true →
      Γ.ctors cn = some (iid, cidx) → RegisteredCtor Γ s'.gdecls cn iid cidx
  /-- `Γ`-agreement for the `casesOn` data of the block just registered. -/
  regCases : ∀ {ii : InductiveVal} {s : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
      {r : InductiveId × InductiveArgMasks} {s' : ErasureState} {w' : Void IO.RealWorld},
    register_inductive ii s ctx cctx ref w = .ok (r, s') w' →
    ∀ {con : Name} {iid : InductiveId} {np : Nat},
      Kername.beq (mutualBlockKn ii) iid.mutualBlockName = true →
      Γ.casesOns con = some (iid, np) →
      ∃ (body : MutualInductiveBody) (oib : OneInductiveBody),
        LBTerm.envLookup s'.gdecls iid.mutualBlockName = some (.inductiveDecl body) ∧
        body.bodies[iid.idx]? = some oib ∧ body.npars = np ∧ oib.propositional = false
  /-- `Γ`-agreement for the field counts of the block just registered. -/
  regFields : ∀ {ii : InductiveVal} {s : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
      {r : InductiveId × InductiveArgMasks} {s' : ErasureState} {w' : Void IO.RealWorld},
    register_inductive ii s ctx cctx ref w = .ok (r, s') w' →
    ∀ {con : Name} {iid : InductiveId} {np : Nat},
      Kername.beq (mutualBlockKn ii) iid.mutualBlockName = true →
      Γ.casesOns con = some (iid, np) → RegisteredCtorFields Γ s'.gdecls iid
  /-- Key distinctness across the recursive block's `gdecls` conses. -/
  recKeys : ∀ {names : List Name} {defs : List (@FixDef LBTerm)} {s : ErasureState},
    RegInvShape Γ s → KeysDistinct (recConstState names defs s).gdecls
  /-- The recursion wall's `closeFix` result: stored `.fix` bodies are closed. -/
  recClosed : ∀ (defs : List (@FixDef LBTerm)) (j : Nat), LBClosed (LBTerm.fix defs j) 0
  /-- `PrepareHyps`-class: `prepare_erasure` does not disturb the registry invariant. -/
  prep : ∀ {e : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
      {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {pe : Expr}
      {s' : ErasureState} {w' : Void IO.RealWorld},
    prepare_erasure e s ctx cctx ref w = .ok (pe, s') w' → RegInvShape Γ s → RegInvShape Γ s'

end LeanToLambdaBox
