import LeanToLambdaBox.Closed
import LeanToLambdaBox.Semantics.Metatheory

/-!
# `substFix`: static fix-closing inverts dynamic fix-unfolding (recursion wall, slice W0)

The shipping eraser builds a recursive block by erasing each sibling body with the
block's own names mapped to fresh **fvars** `ids`, then closing the result with `mkDef`'s
`toBvar` loop — modelled exactly by `closeFix` (`FixMetatheory.lean`). At run time the
target does the opposite: `WcbvEval.fix_guarded` unfolds `defs[idx]` by
`LBTerm.substList (LBTerm.fixSubst defs) defs[idx].body`, replacing the de Bruijn fix
binders by the block's own `.fix defs j` nodes.

This file proves the two are inverse, in the sense the forward simulation needs:
**substituting the block into a `closeFix`-closed body is the same as substituting
`.fix defs j` for `ids[j]` directly in the *open* body**
(`closeFix_substList_fixSubst`). That is the identity `notes/P3_ENV_ERASURE_DESIGN.md`
§1.5 flagged as missing, and it is what will let the β case of the simulations turn a
target fix-unfolding back into an ordinary erasure statement about the source body.

## Contents

* `substFVar` — replace one fvar by a **closed** term (no de Bruijn bookkeeping is needed
  precisely because the replacement is closed), with the usual `Args`/`Alts`/`Defs`
  mutual helpers and their `List.map` forms; `LBClosed.substFVar`.
* `substFVarList` / `substFix` — the simultaneous form; `substFix ids defs` sends
  `.fvar ids[j]` to `.fix defs j`.
* The `toBvar` ↔ `LBTerm.subst` commutation pair — `subst_toBvar_self` (levels agree: the
  fresh bvar is consumed, giving `substFVar`) and `subst_toBvar_succ` (the `toBvar` level
  is above the substitution depth: the binder survives, one lower). These are the
  primitive deferred at `Abstract.lean`'s closing note ("the `toBvar` ↔ `LBTerm.subst`
  commutation … only needed once the bridge substitutes under abstractions"), and they
  are the inductive heart of everything below.
* `closeFixFold_append` / `closeFix_cons` — the structural recursion `closeFix` was
  missing (it is stated on the *pair* list, so peeling an id needs the append law).
* `substList_toBvar`, then `closeFix_substList_fixSubst` and its `_gen` form generalised
  over the base index of the sibling window.

## Hypotheses, and one correction to the design

The capstone needs the block to be **fvar-free at every `ids[j]`**
(`∀ x ∈ ids, ∀ j, ¬ hasFVar x (.fix defs j)`), a hypothesis the design's statement omits.
It is not slack. With `ids = [x₀, x₁]` and `x₀` occurring free in the block, take
`t = .fvar x₁`: the left-hand side substitutes `.fix defs 1` for the closed-off `.bvar 0`
and stops, while the right-hand side goes on to rewrite `x₀` *inside* the inserted node.
The two differ. In the intended use the hypothesis is free: `defs[j].body =
closeFix ids 0 obodies[j]` has every `ids` occurrence already abstracted away.

Conversely `ids.Nodup`, which the design does require, is **not** needed and is not
assumed here: with the fvar-freeness in hand, a repeated id makes both sides agree on the
innermost binding, exactly as `closeFix`'s inner-first fold does.
-/

namespace LeanToLambdaBox

open Lean

/-! ## Part 1 — `substFVar`: replacing an fvar by a closed term

No de Bruijn shifting happens under binders: every lemma below carries `LBClosed s 0`,
and a closed term is fixed by `shift` (`LBClosed.shift_eq`). Structurally recursive via
the same `Args`/`Alts`/`Defs` helper split as `toBvar` (`Basic.lean`). -/

mutual
/-- Replace the free variable `x` by the (closed) term `s` throughout. -/
def substFVar (x : FVarId) (s : LBTerm) : LBTerm → LBTerm
  | .box => .box
  | .bvar i => .bvar i
  | .fvar y => if y == x then s else .fvar y
  | .lambda n b => .lambda n (substFVar x s b)
  | .letIn n v b => .letIn n (substFVar x s v) (substFVar x s b)
  | .app a b => .app (substFVar x s a) (substFVar x s b)
  | .const kn => .const kn
  | .construct iid k args => .construct iid k (substFVarArgs x s args)
  | .case info discr alts => .case info (substFVar x s discr) (substFVarAlts x s alts)
  | .proj p e => .proj p (substFVar x s e)
  | .fix defs i => .fix (substFVarDefs x s defs) i
  | .prim p => .prim p

/-- `substFVar` over a `construct` argument list. -/
def substFVarArgs (x : FVarId) (s : LBTerm) : List LBTerm → List LBTerm
  | [] => []
  | t :: rest => substFVar x s t :: substFVarArgs x s rest

/-- `substFVar` over `case` alternatives. -/
def substFVarAlts (x : FVarId) (s : LBTerm) :
    List (List BinderName × LBTerm) → List (List BinderName × LBTerm)
  | [] => []
  | (ns, b) :: rest => (ns, substFVar x s b) :: substFVarAlts x s rest

/-- `substFVar` over `fix` definitions. -/
def substFVarDefs (x : FVarId) (s : LBTerm) : List (@FixDef LBTerm) → List (@FixDef LBTerm)
  | [] => []
  | fd :: rest => { fd with body := substFVar x s fd.body } :: substFVarDefs x s rest
end

theorem substFVarArgs_eq_map (x : FVarId) (s : LBTerm) (l : List LBTerm) :
    substFVarArgs x s l = l.map (substFVar x s) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [substFVarArgs, List.map, ih]

theorem substFVarAlts_eq_map (x : FVarId) (s : LBTerm) (l : List (List BinderName × LBTerm)) :
    substFVarAlts x s l = l.map (fun a => (a.1, substFVar x s a.2)) := by
  induction l with
  | nil => rfl
  | cons a as ih => obtain ⟨ns, b⟩ := a; simp only [substFVarAlts, List.map, ih]

theorem substFVarDefs_eq_map (x : FVarId) (s : LBTerm) (l : List (@FixDef LBTerm)) :
    substFVarDefs x s l = l.map (fun fd => { fd with body := substFVar x s fd.body }) := by
  induction l with
  | nil => rfl
  | cons fd rest ih => simp only [substFVarDefs, List.map, ih]

/-- `substFVar` preserves de-Bruijn closedness when the substituted term is closed. -/
theorem LBClosed.substFVar {x : FVarId} {s : LBTerm} (hs : LBClosed s 0) :
    ∀ (t : LBTerm) (k : Nat), LBClosed t k →
      LBClosed (LeanToLambdaBox.substFVar x s t) k := by
  intro t
  induction t using LBTerm.recData with
  | hbvar i => exact fun _ h => h
  | hfvar y =>
      intro k _
      show LBClosed (if y == x then s else .fvar y) k
      split
      · exact hs.mono (Nat.zero_le k)
      · trivial
  | hlam n b ih => exact fun k h => ih (k + 1) h
  | hletIn n v b ihv ihb => exact fun k h => ⟨ihv k h.1, ihb (k + 1) h.2⟩
  | happ f a ihf iha => exact fun k h => ⟨ihf k h.1, iha k h.2⟩
  | hconstruct iid c args ih =>
      intro k h
      rw [LBClosed_construct, LBClosedArgs_iff] at h
      show LBClosed (.construct iid c (substFVarArgs x s args)) k
      rw [LBClosed_construct, LBClosedArgs_iff, substFVarArgs_eq_map]
      intro u hu
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hu
      exact ih y hy k (h y hy)
  | hcase info discr alts ihd iha =>
      intro k h
      rw [LBClosed_case, LBClosedAlts_iff] at h
      show LBClosed (.case info (LeanToLambdaBox.substFVar x s discr)
        (substFVarAlts x s alts)) k
      rw [LBClosed_case, LBClosedAlts_iff, substFVarAlts_eq_map]
      refine ⟨ihd k h.1, fun a ha => ?_⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      exact iha y hy _ (h.2 y hy)
  | hproj p e ih => exact fun k h => ih k h
  | hfix defs i ih =>
      intro k h
      rw [LBClosed_fix, LBClosedDefs_iff] at h
      show LBClosed (.fix (substFVarDefs x s defs) i) k
      rw [LBClosed_fix, LBClosedDefs_iff, substFVarDefs_eq_map, List.length_map]
      intro fd hfd
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hfd
      exact ih y hy _ (h y hy)
  | _ => exact fun _ _ => trivial

/-! ### `substFVar` is the identity where the variable does not occur

Mirror of `Abstract.lean`'s `toBvar_eq_of_not_hasFVar`, by the same mutual structural
recursion. Used by `Erases.instFixvars` at the `const_fix`/`fix` arms, where the target is
a closed fvar-free block that the fixvar substitution must leave alone. -/

mutual
theorem substFVar_eq_of_not_hasFVar (x : FVarId) (s : LBTerm) :
    ∀ (t : LBTerm), ¬ hasFVar x t → substFVar x s t = t
  | .box, _ => rfl
  | .bvar _, _ => rfl
  | .fvar y, h => by
    simp only [hasFVar_fvar] at h
    show (if y == x then s else LBTerm.fvar y) = _
    simp [h]
  | .lambda nm body, h => by
    simp only [hasFVar_lambda] at h
    simp only [substFVar, substFVar_eq_of_not_hasFVar x s body h]
  | .letIn nm val body, h => by
    simp only [hasFVar_letIn, not_or] at h
    simp only [substFVar, substFVar_eq_of_not_hasFVar x s val h.1,
      substFVar_eq_of_not_hasFVar x s body h.2]
  | .app a b, h => by
    simp only [hasFVar_app, not_or] at h
    simp only [substFVar, substFVar_eq_of_not_hasFVar x s a h.1,
      substFVar_eq_of_not_hasFVar x s b h.2]
  | .const _, _ => rfl
  | .construct indid k args, h => by
    simp only [hasFVar_construct] at h
    simp only [substFVar, substFVarArgs_eq_of_not_hasFVarArgs x s args h]
  | .case (indid, np) discr alts, h => by
    simp only [hasFVar_case, not_or] at h
    simp only [substFVar, substFVar_eq_of_not_hasFVar x s discr h.1,
      substFVarAlts_eq_of_not_hasFVarAlts x s alts h.2]
  | .proj pinfo e, h => by
    simp only [hasFVar_proj] at h
    simp only [substFVar, substFVar_eq_of_not_hasFVar x s e h]
  | .fix defs i, h => by
    simp only [hasFVar_fix] at h
    simp only [substFVar, substFVarDefs_eq_of_not_hasFVarDefs x s defs h]
  | .prim _, _ => rfl

theorem substFVarArgs_eq_of_not_hasFVarArgs (x : FVarId) (s : LBTerm) :
    ∀ (l : List LBTerm), ¬ hasFVarArgs x l → substFVarArgs x s l = l
  | [], _ => rfl
  | t :: rest, h => by
    simp only [hasFVarArgs, not_or] at h
    simp only [substFVarArgs, substFVar_eq_of_not_hasFVar x s t h.1,
      substFVarArgs_eq_of_not_hasFVarArgs x s rest h.2]

theorem substFVarAlts_eq_of_not_hasFVarAlts (x : FVarId) (s : LBTerm) :
    ∀ (l : List (List BinderName × LBTerm)), ¬ hasFVarAlts x l → substFVarAlts x s l = l
  | [], _ => rfl
  | (ns, b) :: rest, h => by
    simp only [hasFVarAlts, not_or] at h
    simp only [substFVarAlts, substFVar_eq_of_not_hasFVar x s b h.1,
      substFVarAlts_eq_of_not_hasFVarAlts x s rest h.2]

theorem substFVarDefs_eq_of_not_hasFVarDefs (x : FVarId) (s : LBTerm) :
    ∀ (l : List (@FixDef LBTerm)), ¬ hasFVarDefs x l → substFVarDefs x s l = l
  | [], _ => rfl
  | fd :: rest, h => by
    simp only [hasFVarDefs, not_or] at h
    simp only [substFVarDefs, substFVar_eq_of_not_hasFVar x s fd.body h.1,
      substFVarDefs_eq_of_not_hasFVarDefs x s rest h.2]
end

/-- From `l.map f = l` and `u ∈ l`, `f u = u` (elementwise readback of a map fixed
point). Used to descend into the list helpers of `not_hasFVar_of_toBvar_eq_self`. -/
private theorem map_eq_self_elem {α : Type} {f : α → α} {l : List α} (h : l.map f = l)
    {u : α} (hu : u ∈ l) : f u = u := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
  have h2 : (l.map f)[i]? = l[i]? := by rw [h]
  rw [List.getElem?_map, List.getElem?_eq_getElem hi] at h2
  simpa using h2

/-- **The converse of `toBvar_eq_of_not_hasFVar`**: `toBvar` is the identity *only* where
the variable does not occur (otherwise it would have turned an `.fvar` into a `.bvar`).
This is what turns the `const_fix`/`fix` rules' `htobv` inertness premise — all a
derivation carries about its block — into the fvar-freeness `substFVar` needs. The level
is quantified inside the statement, which is what makes the binder cases go through. -/
theorem not_hasFVar_of_toBvar_eq_self (x : FVarId) :
    ∀ (t : LBTerm) (lvl : Nat), toBvar x lvl t = t → ¬ hasFVar x t := by
  intro t
  induction t using LBTerm.recData with
  | hfvar y =>
      intro lvl h
      simp only [hasFVar_fvar]
      intro hy
      rw [show toBvar x lvl (LBTerm.fvar y) = (if y == x then LBTerm.bvar lvl else .fvar y) from rfl,
        if_pos (fvarId_beq_iff_eq.mpr hy)] at h
      exact absurd h (by simp)
  | hlam nm body ih =>
      intro lvl h
      simp only [toBvar, LBTerm.lambda.injEq, true_and] at h
      exact ih (lvl + 1) h
  | hletIn nm val body ihv ihb =>
      intro lvl h
      simp only [toBvar, LBTerm.letIn.injEq, true_and] at h
      simp only [hasFVar_letIn, not_or]
      exact ⟨ihv lvl h.1, ihb (lvl + 1) h.2⟩
  | happ a b iha ihb =>
      intro lvl h
      simp only [toBvar, LBTerm.app.injEq] at h
      simp only [hasFVar_app, not_or]
      exact ⟨iha lvl h.1, ihb lvl h.2⟩
  | hconstruct iid k args ih =>
      intro lvl h
      simp only [toBvar, LBTerm.construct.injEq, true_and, toBvarArgs_eq_map] at h
      simp only [hasFVar_construct, hasFVarArgs_iff]
      rintro ⟨u, hu, hfu⟩
      exact ih u hu lvl (map_eq_self_elem h hu) hfu
  | hcase info discr alts ihd iha =>
      intro lvl h
      simp only [toBvar, LBTerm.case.injEq, true_and, toBvarAlts_eq_map] at h
      simp only [hasFVar_case, not_or, hasFVarAlts_iff]
      refine ⟨ihd lvl h.1, ?_⟩
      rintro ⟨a, ha, hfa⟩
      exact iha a ha (lvl + a.1.length) (congrArg Prod.snd (map_eq_self_elem h.2 ha)) hfa
  | hproj p e ih =>
      intro lvl h
      simp only [toBvar, LBTerm.proj.injEq, true_and] at h
      exact ih lvl h
  | hfix defs i ih =>
      intro lvl h
      simp only [toBvar, LBTerm.fix.injEq, and_true, toBvarDefs_eq_map] at h
      simp only [hasFVar_fix, hasFVarDefs_iff]
      rintro ⟨d, hd, hfd⟩
      exact ih d hd (lvl + defs.length) (congrArg FixDef.body (map_eq_self_elem h hd)) hfd
  | _ => intro _ _; simp

/-! ## Part 2 — the `toBvar` ↔ `subst` commutation pair -/

/-- **Levels agree: the fresh binder is consumed.** Abstracting `x` to level `d` and then
substituting `s` at depth `d` is a direct fvar substitution — provided `t` has no loose
bvar at `d` or above (so the *only* `.bvar d` is the one `toBvar` just created) and `s`
is closed (so the `shift d 0` that `subst` performs is the identity). -/
theorem subst_toBvar_self (x : FVarId) {s : LBTerm} (hs : LBClosed s 0) :
    ∀ (t : LBTerm) (d : Nat), LBClosed t d →
      LBTerm.subst s d (toBvar x d t) = substFVar x s t := by
  intro t
  induction t using LBTerm.recData with
  | hbvar i =>
      intro d hc
      have hlt : i < d := hc
      show LBTerm.subst s d (LBTerm.bvar i) = LBTerm.bvar i
      rw [LBTerm.subst_bvar, if_pos hlt]
  | hfvar y =>
      intro d _
      show LBTerm.subst s d (if y == x then LBTerm.bvar d else LBTerm.fvar y)
        = if y == x then s else LBTerm.fvar y
      by_cases hy : y == x
      · rw [if_pos hy, if_pos hy, LBTerm.subst_bvar, if_neg (Nat.lt_irrefl d), if_pos rfl]
        exact LBClosed.shift_eq hs (Nat.le_refl 0) d
      · rw [if_neg hy, if_neg hy]; rfl
  | hlam n b ih =>
      intro d hc
      show LBTerm.lambda n (LBTerm.subst s (d + 1) (toBvar x (d + 1) b))
        = LBTerm.lambda n (substFVar x s b)
      rw [ih (d + 1) hc]
  | hletIn n v b ihv ihb =>
      intro d hc
      show LBTerm.letIn n (LBTerm.subst s d (toBvar x d v))
          (LBTerm.subst s (d + 1) (toBvar x (d + 1) b))
        = LBTerm.letIn n (substFVar x s v) (substFVar x s b)
      rw [ihv d hc.1, ihb (d + 1) hc.2]
  | happ f a ihf iha =>
      intro d hc
      show LBTerm.app (LBTerm.subst s d (toBvar x d f)) (LBTerm.subst s d (toBvar x d a))
        = LBTerm.app (substFVar x s f) (substFVar x s a)
      rw [ihf d hc.1, iha d hc.2]
  | hconstruct iid c args ih =>
      intro d hc
      rw [LBClosed_construct, LBClosedArgs_iff] at hc
      show LBTerm.construct iid c (LBTerm.substArgs s d (toBvarArgs x d args))
        = LBTerm.construct iid c (substFVarArgs x s args)
      simp only [toBvarArgs_eq_map, LBTerm.substArgs_eq_map, substFVarArgs_eq_map, List.map_map]
      exact congrArg _ (List.map_eq_map_iff.mpr fun u hu => ih u hu d (hc u hu))
  | hcase info discr alts ihd iha =>
      intro d hc
      rw [LBClosed_case, LBClosedAlts_iff] at hc
      show LBTerm.case info (LBTerm.subst s d (toBvar x d discr))
          (LBTerm.substAlts s d (toBvarAlts x d alts))
        = LBTerm.case info (substFVar x s discr) (substFVarAlts x s alts)
      simp only [toBvarAlts_eq_map, LBTerm.substAlts_eq_map, substFVarAlts_eq_map, List.map_map,
        ihd d hc.1]
      refine congrArg _ (List.map_eq_map_iff.mpr fun a ha => ?_)
      show (a.1, LBTerm.subst s (d + a.1.length) (toBvar x (d + a.1.length) a.2))
        = (a.1, substFVar x s a.2)
      rw [iha a ha _ (hc.2 a ha)]
  | hproj p e ih =>
      intro d hc
      show LBTerm.proj p (LBTerm.subst s d (toBvar x d e)) = LBTerm.proj p (substFVar x s e)
      rw [ih d hc]
  | hfix defs i ih =>
      intro d hc
      rw [LBClosed_fix, LBClosedDefs_iff] at hc
      show LBTerm.fix (LBTerm.substDefs s (d + (toBvarDefs x (d + defs.length) defs).length)
          (toBvarDefs x (d + defs.length) defs)) i
        = LBTerm.fix (substFVarDefs x s defs) i
      simp only [toBvarDefs_eq_map, LBTerm.substDefs_eq_map, substFVarDefs_eq_map, List.map_map,
        List.length_map]
      refine congrArg (LBTerm.fix · i) (List.map_eq_map_iff.mpr fun fd hfd => ?_)
      show ({ name := fd.name,
              body := LBTerm.subst s (d + defs.length) (toBvar x (d + defs.length) fd.body),
              principalArgIdx := fd.principalArgIdx } : @FixDef LBTerm)
        = { name := fd.name, body := substFVar x s fd.body,
            principalArgIdx := fd.principalArgIdx }
      rw [ih fd hfd (d + defs.length) (hc fd hfd)]
  | _ => intro d _; rfl

/-- **The `toBvar` level is above the substitution depth: the binder survives, one
lower.** `s` must be closed (so `subst`'s internal `shift` is inert) and must not mention
`x` (otherwise the `toBvar` on the right would reach into the substituted term). -/
theorem subst_toBvar_succ (x : FVarId) {s : LBTerm} (hs : LBClosed s 0)
    (hfv : ¬ hasFVar x s) :
    ∀ (t : LBTerm) (d l : Nat), d ≤ l →
      LBTerm.subst s d (toBvar x (l + 1) t) = toBvar x l (LBTerm.subst s d t) := by
  intro t
  induction t using LBTerm.recData with
  | hbvar i =>
      intro d l _
      show LBTerm.subst s d (LBTerm.bvar i) = toBvar x l (LBTerm.subst s d (LBTerm.bvar i))
      rw [LBTerm.subst_bvar]
      split
      · rfl
      · split
        · rw [LBClosed.shift_eq hs (Nat.le_refl 0) d]
          exact (toBvar_eq_of_not_hasFVar x l s hfv).symm
        · rfl
  | hfvar y =>
      intro d l hdl
      show LBTerm.subst s d (if y == x then LBTerm.bvar (l + 1) else LBTerm.fvar y)
        = toBvar x l (LBTerm.subst s d (LBTerm.fvar y))
      by_cases hy : y == x
      · rw [if_pos hy]
        show LBTerm.subst s d (LBTerm.bvar (l + 1))
          = toBvar x l (LBTerm.fvar y)
        rw [LBTerm.subst_bvar, if_neg (by omega), if_neg (by omega)]
        show LBTerm.bvar (l + 1 - 1) = if y == x then LBTerm.bvar l else LBTerm.fvar y
        rw [if_pos hy]
        exact congrArg _ (by omega)
      · rw [if_neg hy]
        show LBTerm.fvar y = toBvar x l (LBTerm.fvar y)
        show LBTerm.fvar y = if y == x then LBTerm.bvar l else LBTerm.fvar y
        rw [if_neg hy]
  | hlam n b ih =>
      intro d l hdl
      show LBTerm.lambda n (LBTerm.subst s (d + 1) (toBvar x (l + 1 + 1) b))
        = LBTerm.lambda n (toBvar x (l + 1) (LBTerm.subst s (d + 1) b))
      rw [ih (d + 1) (l + 1) (by omega)]
  | hletIn n v b ihv ihb =>
      intro d l hdl
      show LBTerm.letIn n (LBTerm.subst s d (toBvar x (l + 1) v))
          (LBTerm.subst s (d + 1) (toBvar x (l + 1 + 1) b))
        = LBTerm.letIn n (toBvar x l (LBTerm.subst s d v))
          (toBvar x (l + 1) (LBTerm.subst s (d + 1) b))
      rw [ihv d l hdl, ihb (d + 1) (l + 1) (by omega)]
  | happ f a ihf iha =>
      intro d l hdl
      show LBTerm.app (LBTerm.subst s d (toBvar x (l + 1) f))
          (LBTerm.subst s d (toBvar x (l + 1) a))
        = LBTerm.app (toBvar x l (LBTerm.subst s d f)) (toBvar x l (LBTerm.subst s d a))
      rw [ihf d l hdl, iha d l hdl]
  | hconstruct iid c args ih =>
      intro d l hdl
      show LBTerm.construct iid c (LBTerm.substArgs s d (toBvarArgs x (l + 1) args))
        = LBTerm.construct iid c (toBvarArgs x l (LBTerm.substArgs s d args))
      simp only [toBvarArgs_eq_map, LBTerm.substArgs_eq_map, List.map_map]
      exact congrArg _ (List.map_eq_map_iff.mpr fun u hu => ih u hu d l hdl)
  | hcase info discr alts ihd iha =>
      intro d l hdl
      show LBTerm.case info (LBTerm.subst s d (toBvar x (l + 1) discr))
          (LBTerm.substAlts s d (toBvarAlts x (l + 1) alts))
        = LBTerm.case info (toBvar x l (LBTerm.subst s d discr))
          (toBvarAlts x l (LBTerm.substAlts s d alts))
      simp only [toBvarAlts_eq_map, LBTerm.substAlts_eq_map, List.map_map, ihd d l hdl]
      refine congrArg _ (List.map_eq_map_iff.mpr fun a ha => ?_)
      show (a.1, LBTerm.subst s (d + a.1.length) (toBvar x (l + 1 + a.1.length) a.2))
        = (a.1, toBvar x (l + a.1.length) (LBTerm.subst s (d + a.1.length) a.2))
      rw [show l + 1 + a.1.length = (l + a.1.length) + 1 from by omega,
        iha a ha (d + a.1.length) (l + a.1.length) (by omega)]
  | hproj p e ih =>
      intro d l hdl
      show LBTerm.proj p (LBTerm.subst s d (toBvar x (l + 1) e))
        = LBTerm.proj p (toBvar x l (LBTerm.subst s d e))
      rw [ih d l hdl]
  | hfix defs i ih =>
      intro d l hdl
      show LBTerm.fix (LBTerm.substDefs s (d + (toBvarDefs x (l + 1 + defs.length) defs).length)
          (toBvarDefs x (l + 1 + defs.length) defs)) i
        = LBTerm.fix (toBvarDefs x (l + (LBTerm.substDefs s (d + defs.length) defs).length)
          (LBTerm.substDefs s (d + defs.length) defs)) i
      simp only [toBvarDefs_eq_map, LBTerm.substDefs_eq_map, List.map_map, List.length_map]
      refine congrArg (LBTerm.fix · i) (List.map_eq_map_iff.mpr fun fd hfd => ?_)
      show ({ name := fd.name,
              body := LBTerm.subst s (d + defs.length) (toBvar x (l + 1 + defs.length) fd.body),
              principalArgIdx := fd.principalArgIdx } : @FixDef LBTerm)
        = { name := fd.name,
            body := toBvar x (l + defs.length) (LBTerm.subst s (d + defs.length) fd.body),
            principalArgIdx := fd.principalArgIdx }
      rw [show l + 1 + defs.length = (l + defs.length) + 1 from by omega,
        ih fd hfd (d + defs.length) (l + defs.length) (by omega)]
  | _ => intro d l _; rfl

/-! ## Part 3 — the simultaneous forms -/

/-- Iterated `substFVar`, innermost (list-tail) binding applied first. -/
def substFVarList : List (FVarId × LBTerm) → LBTerm → LBTerm
  | [], t => t
  | (x, s) :: rest, t => substFVar x s (substFVarList rest t)

theorem LBClosed.substFVarList :
    ∀ (l : List (FVarId × LBTerm)), (∀ p ∈ l, LBClosed p.2 0) →
      ∀ (t : LBTerm) (k : Nat), LBClosed t k →
        LBClosed (LeanToLambdaBox.substFVarList l t) k := by
  intro l
  induction l with
  | nil => exact fun _ _ _ ht => ht
  | cons p rest ih =>
      obtain ⟨x, s⟩ := p
      intro hl t k ht
      exact LBClosed.substFVar (hl (x, s) (List.mem_cons_self ..)) _ k
        (ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) t k ht)

/-- **`substFix ids defs`** — the block's own fix nodes substituted for the block's
fixvars: `.fvar ids[j] ↦ .fix defs j`. This is the *static* counterpart of
`WcbvEval.fix_guarded`'s dynamic `LBTerm.substList (LBTerm.fixSubst defs)`. -/
def substFix (ids : List FVarId) (defs : List (@FixDef LBTerm)) (t : LBTerm) : LBTerm :=
  substFVarList (ids.zipIdx.map (fun p => (p.1, LBTerm.fix defs p.2))) t

/-! ## Part 3b — `substFVarList`/`substFix` push through every node (recursion wall, W3.1)

`Erases.instFixvars` (`RecBlockErasure`) is an induction over an erasure derivation whose
*target* is being rewritten by `substFix`, so every structural rule needs the matching
"`substFix` commutes with this node" equation. Each is the corresponding `substFVar`
clause, iterated down the substitution list. -/

@[simp] theorem substFVarList_box (L : List (FVarId × LBTerm)) :
    substFVarList L .box = .box := by
  induction L with
  | nil => rfl
  | cons p rest ih => obtain ⟨y, s⟩ := p; simp only [substFVarList, ih]; rfl

@[simp] theorem substFVarList_bvar (L : List (FVarId × LBTerm)) (i : Nat) :
    substFVarList L (.bvar i) = .bvar i := by
  induction L with
  | nil => rfl
  | cons p rest ih => obtain ⟨y, s⟩ := p; simp only [substFVarList, ih]; rfl

@[simp] theorem substFVarList_const (L : List (FVarId × LBTerm)) (kn : Kername) :
    substFVarList L (.const kn) = .const kn := by
  induction L with
  | nil => rfl
  | cons p rest ih => obtain ⟨y, s⟩ := p; simp only [substFVarList, ih]; rfl

@[simp] theorem substFVarList_lambda (L : List (FVarId × LBTerm)) (n : BinderName)
    (b : LBTerm) : substFVarList L (.lambda n b) = .lambda n (substFVarList L b) := by
  induction L with
  | nil => rfl
  | cons p rest ih => obtain ⟨y, s⟩ := p; simp only [substFVarList, ih]; rfl

@[simp] theorem substFVarList_letIn (L : List (FVarId × LBTerm)) (n : BinderName)
    (v b : LBTerm) :
    substFVarList L (.letIn n v b) = .letIn n (substFVarList L v) (substFVarList L b) := by
  induction L with
  | nil => rfl
  | cons p rest ih => obtain ⟨y, s⟩ := p; simp only [substFVarList, ih]; rfl

@[simp] theorem substFVarList_app (L : List (FVarId × LBTerm)) (f a : LBTerm) :
    substFVarList L (.app f a) = .app (substFVarList L f) (substFVarList L a) := by
  induction L with
  | nil => rfl
  | cons p rest ih => obtain ⟨y, s⟩ := p; simp only [substFVarList, ih]; rfl

/-- (Projection round, slice P1.) The `.app` twin: `substFVar` is inert in a
`ProjectionInfo`, so a fvar substitution goes straight through a projection node. -/
@[simp] theorem substFVarList_proj (L : List (FVarId × LBTerm)) (pinfo : ProjectionInfo)
    (e : LBTerm) :
    substFVarList L (.proj pinfo e) = .proj pinfo (substFVarList L e) := by
  induction L with
  | nil => rfl
  | cons q rest ih => obtain ⟨y, s⟩ := q; simp only [substFVarList, ih]; rfl

theorem substFVarList_construct (L : List (FVarId × LBTerm)) (iid : InductiveId) (k : Nat)
    (args : List LBTerm) :
    substFVarList L (.construct iid k args) = .construct iid k (args.map (substFVarList L)) := by
  induction L with
  | nil => simp [substFVarList]
  | cons p rest ih =>
      obtain ⟨y, s⟩ := p
      simp only [substFVarList, ih]
      show LBTerm.construct iid k (substFVarArgs y s _) = _
      simp only [substFVarArgs_eq_map, List.map_map]
      rfl

theorem substFVarList_case (L : List (FVarId × LBTerm)) (info : InductiveId × Nat)
    (discr : LBTerm) (alts : List (List BinderName × LBTerm)) :
    substFVarList L (.case info discr alts)
      = .case info (substFVarList L discr) (alts.map (fun a => (a.1, substFVarList L a.2))) := by
  induction L with
  | nil => simp [substFVarList]
  | cons p rest ih =>
      obtain ⟨y, s⟩ := p
      simp only [substFVarList, ih]
      show LBTerm.case info _ (substFVarAlts y s _) = _
      simp only [substFVarAlts_eq_map, List.map_map]
      rfl

/-- On a term the substitution list does not mention, it is the identity. -/
theorem substFVarList_eq_self_of_not_hasFVar :
    ∀ (L : List (FVarId × LBTerm)) (t : LBTerm), (∀ p ∈ L, ¬ hasFVar p.1 t) →
      substFVarList L t = t := by
  intro L
  induction L with
  | nil => intro _ _; rfl
  | cons p rest ih =>
      intro t h
      obtain ⟨y, s⟩ := p
      show substFVar y s (substFVarList rest t) = t
      rw [ih t (fun q hq => h q (List.mem_cons_of_mem _ hq))]
      exact substFVar_eq_of_not_hasFVar y s t (h (y, s) (List.mem_cons_self ..))

/-- `substFix ids defs` sends `.fvar ids[j]` to the block's `j`-th node — the whole point
of the operation. Generalised over the window's base index, as `closeFix`'s capstone is;
`hfv` (the block does not mention the fixvars) is the same hypothesis, and it is what lets
an already-substituted sibling pass through the remaining substitutions untouched. -/
theorem substFVarList_zipIdx_fvar {defs : List (@FixDef LBTerm)} :
    ∀ (ids : List FVarId), ids.Nodup → (∀ x ∈ ids, ∀ j, ¬ hasFVar x (LBTerm.fix defs j)) →
      ∀ (base j : Nat) (h : j < ids.length),
        substFVarList ((ids.zipIdx base).map (fun p => (p.1, LBTerm.fix defs p.2)))
            (.fvar (ids[j]'h))
          = .fix defs (base + j) := by
  intro ids
  induction ids with
  | nil => intro _ _ base j h; exact absurd h (by simp)
  | cons x rest ih =>
      intro hnd hfv base j h
      have hxr : x ∉ rest := by simpa using (List.nodup_cons.mp hnd).1
      have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hfv' : ∀ y ∈ rest, ∀ j, ¬ hasFVar y (LBTerm.fix defs j) :=
        fun y hy => hfv y (List.mem_cons_of_mem _ hy)
      rw [List.zipIdx_cons, List.map_cons]
      show substFVar x (LBTerm.fix defs base)
        (substFVarList ((rest.zipIdx (base + 1)).map (fun p => (p.1, LBTerm.fix defs p.2))) _) = _
      match j, h with
      | 0, _ =>
          have hinner : substFVarList
              ((rest.zipIdx (base + 1)).map (fun p => (p.1, LBTerm.fix defs p.2)))
              (.fvar x) = .fvar x := by
            refine substFVarList_eq_self_of_not_hasFVar _ _ (fun p hp => ?_)
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
            have : q.1 ∈ rest := List.fst_mem_of_mem_zipIdx hq
            simp only [hasFVar_fvar]
            intro he; exact hxr (he ▸ this)
          show substFVar x (LBTerm.fix defs base) (substFVarList _ (LBTerm.fvar x)) = _
          rw [hinner]
          show (if x == x then LBTerm.fix defs base else LBTerm.fvar x) = _
          simp
      | k + 1, h =>
          have hk : k < rest.length := by simpa using h
          show substFVar x (LBTerm.fix defs base)
            (substFVarList _ (LBTerm.fvar (rest[k]'hk))) = _
          rw [ih hnd' hfv' (base + 1) k hk]
          rw [substFVar_eq_of_not_hasFVar x _ _ (hfv x (List.mem_cons_self ..) _)]
          congr 1
          omega

/-- The `base = 0` instance, in the `substFix` spelling. -/
theorem substFix_fvar_getElem {ids : List FVarId} {defs : List (@FixDef LBTerm)}
    (hnd : ids.Nodup) (hfv : ∀ x ∈ ids, ∀ j, ¬ hasFVar x (LBTerm.fix defs j))
    (j : Nat) (h : j < ids.length) :
    substFix ids defs (.fvar (ids[j]'h)) = .fix defs j := by
  show substFVarList ((ids.zipIdx).map (fun p => (p.1, LBTerm.fix defs p.2))) _ = _
  rw [show ids.zipIdx = ids.zipIdx 0 from rfl,
    substFVarList_zipIdx_fvar ids hnd hfv 0 j h]
  simp

/-! ## Part 4 — `closeFix`'s structural recursion

`closeFix` is stated on the *pair* list (`ids.reverse.zipIdx base`), so peeling one id
needs the append law for `closeFixFold` first. -/

theorem closeFixFold_append (p q : List (FVarId × Nat)) (t : LBTerm) :
    closeFixFold (p ++ q) t = closeFixFold q (closeFixFold p t) := by
  induction p generalizing t with
  | nil => rfl
  | cons a as ih => obtain ⟨y, lvl⟩ := a; rw [List.cons_append, closeFixFold_cons, ih]; rfl

@[simp] theorem closeFix_nil (base : Nat) (t : LBTerm) : closeFix [] base t = t := rfl

/-- Peeling the **head** id: it is the outermost `toBvar`, at the top of the telescope
(`base + rest.length`). -/
theorem closeFix_cons (x : FVarId) (rest : List FVarId) (base : Nat) (t : LBTerm) :
    closeFix (x :: rest) base t = toBvar x (base + rest.length) (closeFix rest base t) := by
  show closeFixFold ((x :: rest).reverse.zipIdx base) t = _
  rw [List.reverse_cons, List.zipIdx_append, List.length_reverse, closeFixFold_append]
  rfl

/-! ## Part 5 — the capstone -/

/-- Pushing a simultaneous substitution of closed, `x`-free terms past an abstraction of
`x`: the `toBvar` level drops by exactly the number of substitutions. -/
theorem substList_toBvar (x : FVarId) :
    ∀ (ss : List LBTerm), (∀ s ∈ ss, LBClosed s 0) → (∀ s ∈ ss, ¬ hasFVar x s) →
      ∀ (w : LBTerm),
        LBTerm.substList ss (toBvar x ss.length w) = toBvar x 0 (LBTerm.substList ss w) := by
  intro ss
  induction ss with
  | nil => intro _ _ w; rfl
  | cons a as ih =>
      intro hcl hfv w
      have hstep : LBTerm.subst a 0 (toBvar x (as.length + 1) w)
          = toBvar x as.length (LBTerm.subst a 0 w) :=
        subst_toBvar_succ x (hcl a (List.mem_cons_self ..)) (hfv a (List.mem_cons_self ..))
          w 0 as.length (Nat.zero_le _)
      show LBTerm.substList as (LBTerm.subst1 a (toBvar x (as.length + 1) w))
        = toBvar x 0 (LBTerm.substList as (LBTerm.subst1 a w))
      rw [LBTerm.subst1, hstep,
        ih (fun s hs => hcl s (List.mem_cons_of_mem _ hs))
           (fun s hs => hfv s (List.mem_cons_of_mem _ hs)) (LBTerm.subst a 0 w)]
      rfl

/-- `substList_toBvar` at a definitionally-supplied length. -/
theorem substList_toBvar' (x : FVarId) {ss : List LBTerm} (hcl : ∀ s ∈ ss, LBClosed s 0)
    (hfv : ∀ s ∈ ss, ¬ hasFVar x s) {n : Nat} (hn : ss.length = n) (w : LBTerm) :
    LBTerm.substList ss (toBvar x n w) = toBvar x 0 (LBTerm.substList ss w) := by
  subst hn; exact substList_toBvar x ss hcl hfv w

/-- The capstone, generalised over the base index of the sibling window: the induction
peels one id at a time, and the surviving suffix of the block starts at `base`. -/
theorem closeFix_substList_fixSubst_gen {defs : List (@FixDef LBTerm)}
    (hdefs : ∀ j, LBClosed (LBTerm.fix defs j) 0) :
    ∀ (ids : List FVarId), (∀ x ∈ ids, ∀ j, ¬ hasFVar x (LBTerm.fix defs j)) →
      ∀ (base : Nat) (t : LBTerm), LBClosed t 0 →
        LBTerm.substList
            (((List.range' base ids.length).reverse).map (fun j => LBTerm.fix defs j))
            (closeFix ids 0 t)
          = substFVarList ((ids.zipIdx base).map (fun p => (p.1, LBTerm.fix defs p.2))) t := by
  intro ids
  induction ids with
  | nil => intro _ base t _; rfl
  | cons x rest ih =>
      intro hfv base t hcl
      have hfvx : ∀ j, ¬ hasFVar x (LBTerm.fix defs j) := hfv x (List.mem_cons_self ..)
      have hfvr : ∀ y ∈ rest, ∀ j, ¬ hasFVar y (LBTerm.fix defs j) :=
        fun y hy => hfv y (List.mem_cons_of_mem _ hy)
      have hsslen :
          (((List.range' (base + 1) rest.length).reverse).map
            (fun j => LBTerm.fix defs j)).length = rest.length := by
        rw [List.length_map, List.length_reverse, List.length_range']
      have hsscl : ∀ s ∈ ((List.range' (base + 1) rest.length).reverse).map
          (fun j => LBTerm.fix defs j), LBClosed s 0 := by
        intro s hs; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hs; exact hdefs j
      have hssfv : ∀ s ∈ ((List.range' (base + 1) rest.length).reverse).map
          (fun j => LBTerm.fix defs j), ¬ hasFVar x s := by
        intro s hs; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hs; exact hfvx j
      have hwin : ((List.range' base (rest.length + 1)).reverse).map (fun j => LBTerm.fix defs j)
          = (((List.range' (base + 1) rest.length).reverse).map (fun j => LBTerm.fix defs j))
            ++ [LBTerm.fix defs base] := by
        rw [show List.range' base (rest.length + 1)
              = base :: List.range' (base + 1) rest.length from rfl,
          List.reverse_cons, List.map_append]
        rfl
      have hUcl : LBClosed
          (substFVarList ((rest.zipIdx (base + 1)).map
            (fun p => (p.1, LBTerm.fix defs p.2))) t) 0 :=
        LBClosed.substFVarList _ (fun p hp => by
          obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp; exact hdefs q.2) t 0 hcl
      rw [List.length_cons, hwin, LBTerm.substList_concat, closeFix_cons, Nat.zero_add,
        substList_toBvar' x hsscl hssfv hsslen, ih hfvr (base + 1) t hcl,
        List.zipIdx_cons, List.map_cons]
      show LBTerm.subst1 (LBTerm.fix defs base) (toBvar x 0 _)
        = substFVar x (LBTerm.fix defs base) _
      rw [LBTerm.subst1, subst_toBvar_self x (hdefs base) _ 0 hUcl]

/-- **Unfolding a closed fix block undoes `mkDef`'s closing.** Substituting the block
into a `closeFix`-closed body — `LBTerm.substList (LBTerm.fixSubst defs)`, exactly what
`WcbvEval.fix_guarded` performs — is the same as substituting `.fix defs j` for `ids[j]`
in the *open* body.

Hypotheses: `hdefs` (every `.fix defs j` is closed) and `hfv` (the block does not mention
the fixvars — automatic when the block was itself produced by `closeFix ids`). `ids.Nodup`
is *not* required; see the module docstring. -/
theorem closeFix_substList_fixSubst {ids : List FVarId} {defs : List (@FixDef LBTerm)}
    (hilen : ids.length = defs.length)
    (hdefs : ∀ j, LBClosed (LBTerm.fix defs j) 0)
    (hfv : ∀ x ∈ ids, ∀ j, ¬ hasFVar x (LBTerm.fix defs j))
    {t : LBTerm} (hcl : LBClosed t 0) :
    LBTerm.substList (LBTerm.fixSubst defs) (closeFix ids 0 t) = substFix ids defs t := by
  have hfs : LBTerm.fixSubst defs
      = ((List.range' 0 ids.length).reverse).map (fun j => LBTerm.fix defs j) := by
    rw [hilen, LBTerm.fixSubst, List.range_eq_range']
  rw [hfs, substFix, closeFix_substList_fixSubst_gen hdefs ids hfv 0 t hcl]

/-! ## Part 6 — non-vacuity

The single-def self-loop `fix f. f` (the shape `EnvErasureRec`'s fixture registers) with
its own fixvar: closing `.fvar x` gives `.bvar 0`, and unfolding that gives the block
back. Both premises of the capstone are discharged, and it fires on a real value. -/

private def nvDefs : List (@FixDef LBTerm) := [{ name := .named "f", body := .bvar 0 }]

theorem closeFix_substList_fixSubst_fires (x : FVarId) :
    LBTerm.substList (LBTerm.fixSubst nvDefs) (closeFix [x] 0 (.fvar x))
      = substFix [x] nvDefs (.fvar x) := by
  refine closeFix_substList_fixSubst (ids := [x]) rfl (fun j => ?_) (fun y _ j => ?_) trivial
  · exact ⟨Nat.zero_lt_one, trivial⟩
  · simp only [nvDefs, hasFVar_fix, hasFVarDefs, hasFVar_bvar, or_self, not_false_iff]

/-- …and the common value is the block itself, not a vacuous `.bvar`. -/
theorem closeFix_substList_fixSubst_fires_value (x : FVarId) :
    LBTerm.substList (LBTerm.fixSubst nvDefs) (closeFix [x] 0 (.fvar x))
      = .fix nvDefs 0 := by
  rw [closeFix_substList_fixSubst_fires x]
  show substFVar x (LBTerm.fix nvDefs 0) (.fvar x) = _
  show (if x == x then LBTerm.fix nvDefs 0 else LBTerm.fvar x) = _
  simp

/-! ## Part 7 — the unfolding chain (recursion wall, slice W2)

Slice W1's `Erases.fix` states its bodies premise against the *one-step* unfolding
`LBTerm.substList (LBTerm.fixSubst defs) defs[idx].body` — precisely
`WcbvEval.fix_guarded`'s reduct. Usually one step is all the β case of a forward
simulation needs: the unfolding of a real recursive body is `.lambda`-headed (or `.box`),
and the target's `fix_guarded` is immediately followed by a `beta` (or an `app_box`).

But a *degenerate* block can unfold to another `.fix` node — `defs[idx].body = .bvar j`
gives `.fix defs j` back — and then the target must fire `fix_guarded` again. The number
of such steps is not bounded by anything in the β case's induction (which is on the
*source* derivation), so it is packaged here as its own relation: `FixUnfoldChain defs
idx u` says `u` is reached from `.fix defs idx` by a finite, non-empty chain of one-step
unfoldings, each of whose selected definitions has the `mkDef` default `principalArgIdx`.
`Erases.fix_unfold` (`ErasesCorrect`) produces such a chain from a `.lam`-to-`.fix`
erasure, by induction on the erasure derivation, with `u` guaranteed *not* to be a `.fix`;
`FixUnfoldChain.eval` below turns it into the corresponding stack of `fix_guarded` nodes.
-/

/-- `FixUnfoldChain defs idx u`: `u` is the result of unfolding `.fix defs idx` one or
more times, each step selecting a definition whose `principalArgIdx` is the `mkDef`
default `0` (which is what makes the step consume exactly one argument). -/
inductive FixUnfoldChain : List (@FixDef LBTerm) → Nat → LBTerm → Prop
  /-- One unfolding: `.fix defs idx ↦ substList (fixSubst defs) defs[idx].body`. -/
  | step {defs : List (@FixDef LBTerm)} {idx : Nat} (hidx : idx < defs.length)
      (hrarg : ∀ d ∈ defs, d.principalArgIdx = 0) :
      FixUnfoldChain defs idx
        (LBTerm.substList (LBTerm.fixSubst defs) (defs[idx]'hidx).body)
  /-- The unfolding is itself a `.fix` node; keep going. -/
  | trans {defs : List (@FixDef LBTerm)} {idx : Nat}
      {defs' : List (@FixDef LBTerm)} {idx' : Nat} {u : LBTerm}
      (hidx : idx < defs.length) (hrarg : ∀ d ∈ defs, d.principalArgIdx = 0)
      (heq : LBTerm.substList (LBTerm.fixSubst defs) (defs[idx]'hidx).body
               = .fix defs' idx')
      (h : FixUnfoldChain defs' idx' u) :
      FixUnfoldChain defs idx u

/-- A target term either *is* a `fix` node or is provably none — the case split
`Erases.fix_unfold` iterates on. -/
theorem LBTerm.fix_or_not (t : LBTerm) :
    (∃ (defs : List (@FixDef LBTerm)) (i : Nat), t = .fix defs i) ∨
    (∀ (defs : List (@FixDef LBTerm)) (i : Nat), t ≠ .fix defs i) := by
  cases t with
  | fix defs i => exact .inl ⟨defs, i, rfl⟩
  | _ => exact .inr (fun _ _ => by simp)

/-- **The chain is a stack of `fix_guarded` steps.** If the function part of an
application evaluates to the block and the argument to `av`, then evaluating the
application is the same as evaluating the chain's end applied to `av`. Each link is one
`WcbvEval.fix_guarded` with an empty accumulated spine (`argsv = []`, forced by
`principalArgIdx = 0`), so **one source β-step matches one `fix_guarded` per link plus
the final application step**. -/
theorem FixUnfoldChain.eval {E : GlobalDeclarations} {fl : WcbvFlags}
    (hg : fl.with_guarded_fix = true)
    {defs : List (@FixDef LBTerm)} {idx : Nat} {u : LBTerm}
    (hch : FixUnfoldChain defs idx u) :
    ∀ {f a av r : LBTerm}, WcbvEval E fl f (.fix defs idx) → WcbvEval E fl a av →
      WcbvEval E fl (.app u av) r → WcbvEval E fl (.app f a) r := by
  induction hch with
  | step hidx hrarg =>
      intro f a av r hf ha hr
      exact .fix_guarded (argsv := []) hg hf ha (List.getElem?_eq_getElem hidx)
        (hrarg _ (List.getElem_mem hidx)) hr
  | trans hidx hrarg heq _ ih =>
      intro f a av r hf ha hr
      refine .fix_guarded (argsv := []) hg hf ha (List.getElem?_eq_getElem hidx)
        (hrarg _ (List.getElem_mem hidx)) ?_
      show WcbvEval E fl (.app (LBTerm.substList (LBTerm.fixSubst _) _) av) r
      rw [heq]
      exact ih (.fix_atom _ _) (value_final (eval_to_value ha)) hr

/-- **The chain preserves closedness.** Every entry of `fixSubst defs` is a `.fix defs j`,
which is closed exactly when the block is, and `defs[idx].body` is closed under
`defs.length` binders — so one unfolding lands on a closed term, and the chain iterates
it. Needed by the ι simulation, which threads `LBClosed t 0`. -/
theorem FixUnfoldChain.lbClosed {defs : List (@FixDef LBTerm)} {idx : Nat} {u : LBTerm}
    (hch : FixUnfoldChain defs idx u) : LBClosed (.fix defs idx) 0 → LBClosed u 0 := by
  have hstep : ∀ (defs : List (@FixDef LBTerm)) (idx : Nat) (hidx : idx < defs.length),
      LBClosed (LBTerm.fix defs idx) 0 →
      LBClosed (LBTerm.substList (LBTerm.fixSubst defs) (defs[idx]'hidx).body) 0 := by
    intro defs idx hidx hcl
    have hbody : LBClosed (defs[idx]'hidx).body (LBTerm.fixSubst defs).length := by
      rw [LBTerm.fixSubst, List.length_map, List.length_reverse, List.length_range]
      rw [LBClosed_fix, LBClosedDefs_iff] at hcl
      have := hcl _ (List.getElem_mem hidx)
      rwa [Nat.zero_add] at this
    refine LBClosed.substList (fun s hs => ?_) hbody
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hs
    rw [LBClosed_fix, LBClosedDefs_iff] at hcl ⊢
    exact hcl
  induction hch with
  | step hidx hrarg => exact fun hcl => hstep _ _ hidx hcl
  | trans hidx hrarg heq _ ih => exact fun hcl => ih (heq ▸ hstep _ _ hidx hcl)

/-- Non-vacuity: the self-loop block `fix f. #0` unfolds to itself, so `FixUnfoldChain`
has derivations of every length — the situation the `trans` link exists for. -/
theorem fixUnfoldChain_selfLoop_step :
    FixUnfoldChain nvDefs 0 (.fix nvDefs 0) := by
  have h : LBTerm.substList (LBTerm.fixSubst nvDefs)
      ((nvDefs[0]'(by simp [nvDefs])).body) = .fix nvDefs 0 := by
    simp [nvDefs, LBTerm.fixSubst, LBTerm.substList, LBTerm.subst1, LBTerm.subst,
      LBTerm.shift, LBTerm.shiftDefs]
  exact h ▸ FixUnfoldChain.step (by simp [nvDefs]) (by simp [nvDefs])

/-! ## Part 5 — the fvar kit: what closing removes, and what it leaves

`Abstract.lean` says when `toBvar` is *inert* (`toBvar_eq_of_not_hasFVar` and its converse
`not_hasFVar_of_toBvar_eq_self`, above). What the block-level closing needs is the
complementary, quantitative statement: `toBvar y` deletes exactly the occurrences of `y`
and manufactures none, so an `n`-way `closeFix` over `ids` deletes exactly the `ids` — and
a term whose free variables are all in `ids` closes to a term with **no** free variable at
all.

This is what turns "the block's opened bodies mention only the run's fixvars" into "the
stored `.fix` node is fvar-free", the hypothesis the `closeFix_substList_fixSubst` capstone
above (and, downstream, `RecBlockErasure.erases_fix_of_closed`) asks for. Before this kit it
had to be assumed by every caller. -/

/-- **`toBvar` removes exactly one variable and creates none.** If `x` occurs in
`toBvar y lvl t` then `x` is not `y` (that variable is precisely what the abstraction sent
to a `.bvar`) and `x` already occurred in `t` (abstraction introduces no `fvar` node). The
level is quantified inside the statement, as in `not_hasFVar_of_toBvar_eq_self`, so the
binder cases can hand the incremented level to the induction hypothesis. -/
theorem hasFVar_toBvar (x y : FVarId) :
    ∀ (t : LBTerm) (lvl : Nat), hasFVar x (toBvar y lvl t) → x ≠ y ∧ hasFVar x t := by
  intro t
  induction t using LBTerm.recData with
  | hfvar z =>
      intro lvl h
      rw [show toBvar y lvl (LBTerm.fvar z)
            = (if z == y then LBTerm.bvar lvl else .fvar z) from rfl] at h
      split at h
      · exact absurd h (by simp)
      · rename_i hzy
        simp only [hasFVar_fvar] at h ⊢
        exact ⟨fun hxy => hzy (fvarId_beq_iff_eq.mpr (h.trans hxy)), h⟩
  | hlam nm body ih =>
      intro lvl h
      simp only [toBvar, hasFVar_lambda] at h
      exact ih (lvl + 1) h
  | hletIn nm val body ihv ihb =>
      intro lvl h
      simp only [toBvar, hasFVar_letIn] at h
      simp only [hasFVar_letIn]
      rcases h with h | h
      · exact ⟨(ihv lvl h).1, .inl (ihv lvl h).2⟩
      · exact ⟨(ihb (lvl + 1) h).1, .inr (ihb (lvl + 1) h).2⟩
  | happ a b iha ihb =>
      intro lvl h
      simp only [toBvar, hasFVar_app] at h
      simp only [hasFVar_app]
      rcases h with h | h
      · exact ⟨(iha lvl h).1, .inl (iha lvl h).2⟩
      · exact ⟨(ihb lvl h).1, .inr (ihb lvl h).2⟩
  | hconstruct iid k args ih =>
      intro lvl h
      simp only [toBvar, hasFVar_construct, toBvarArgs_eq_map, hasFVarArgs_iff] at h
      obtain ⟨u, hu, hxu⟩ := h
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
      obtain ⟨hne, hxv⟩ := ih v hv lvl hxu
      refine ⟨hne, ?_⟩
      simp only [hasFVar_construct, hasFVarArgs_iff]
      exact ⟨v, hv, hxv⟩
  | hcase info discr alts ihd iha =>
      intro lvl h
      simp only [toBvar, hasFVar_case, toBvarAlts_eq_map, hasFVarAlts_iff] at h
      simp only [hasFVar_case, hasFVarAlts_iff]
      rcases h with h | ⟨a, ha, hxa⟩
      · exact ⟨(ihd lvl h).1, .inl (ihd lvl h).2⟩
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        obtain ⟨hne, hxb⟩ := iha b hb (lvl + b.1.length) hxa
        exact ⟨hne, .inr ⟨b, hb, hxb⟩⟩
  | hproj p e ih =>
      intro lvl h
      simp only [toBvar, hasFVar_proj] at h
      exact ih lvl h
  | hfix defs i ih =>
      intro lvl h
      simp only [toBvar, hasFVar_fix, toBvarDefs_eq_map, hasFVarDefs_iff] at h
      obtain ⟨d, hd, hxd⟩ := h
      obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
      obtain ⟨hne, hxd'⟩ := ih d' hd' (lvl + defs.length) hxd
      refine ⟨hne, ?_⟩
      simp only [hasFVar_fix, hasFVarDefs_iff]
      exact ⟨d', hd', hxd'⟩
  | _ => intro lvl h; simp [toBvar] at h

/-- **The fold closes everything it is given.** If every free variable of `t` is scheduled
for abstraction by `pairs`, then `closeFixFold pairs t` has no free variable left: each
step deletes its own variable (`hasFVar_toBvar`) and adds none, so the remaining steps
face a term whose free variables are exactly the still-scheduled ones. -/
theorem not_hasFVar_closeFixFold :
    ∀ (pairs : List (FVarId × Nat)) (t : LBTerm),
      (∀ z, hasFVar z t → z ∈ pairs.map Prod.fst) →
      ∀ x, ¬ hasFVar x (closeFixFold pairs t) := by
  intro pairs
  induction pairs with
  | nil =>
      intro t h x hx
      rw [closeFixFold_nil] at hx
      simpa using h x hx
  | cons p rest ih =>
      obtain ⟨y, lvl⟩ := p
      intro t h x hx
      rw [closeFixFold_cons] at hx
      refine ih (toBvar y lvl t) (fun z hz => ?_) x hx
      obtain ⟨hzy, hzt⟩ := hasFVar_toBvar z y t lvl hz
      have hmem := h z hzt
      simp only [List.map_cons, List.mem_cons] at hmem
      exact hmem.resolve_left hzy

/-- **The block-level form.** A term whose free variables all lie in `ids` closes to a
term with none: `closeFix ids base` is `closeFixFold` over `ids.reverse.zipIdx base`, whose
first projection is `ids.reverse`. This is what makes the stored `.fix` node fvar-free
without assuming it — the block's opened bodies mention only the run's own fixvars, and
`mkDef` abstracts exactly those. -/
theorem not_hasFVar_closeFix {ids : List FVarId} {t : LBTerm}
    (h : ∀ z, hasFVar z t → z ∈ ids) (base : Nat) (x : FVarId) :
    ¬ hasFVar x (closeFix ids base t) := by
  refine not_hasFVar_closeFixFold (ids.reverse.zipIdx base) t (fun z hz => ?_) x
  rw [List.zipIdx_map_fst, List.mem_reverse]
  exact h z hz

end LeanToLambdaBox
