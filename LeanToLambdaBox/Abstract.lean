import LeanToLambdaBox.Basic
import LeanToLambdaBox.Semantics.Substitution

/-!
# Metatheory of `abstract`/`toBvar` (fvar → de Bruijn) — foundation

Foundation for the `fvar`↔de-Bruijn reconciliation between the shipping erasure
(`Erasure.visitExpr`, which opens binders into fresh `fvar`s, recurses, then
`abstract`s back to de Bruijn) and the pure de-Bruijn model (`eraseCore`/`Erases`).

These lemmas were **unprovable while `toBvar` was a `partial def`**; de-partializing
it (`Basic.lean`) into a structural `def` with explicit list helpers is what makes
them available — a concrete instance of the de-partialization technique that the
shipping `visitExpr` family will also need.

`toBvar x lvl` replaces the free variable `x` by the de Bruijn index `lvl`,
incrementing under binders — the LBTerm analogue of "close the binder".
-/

namespace LeanToLambdaBox

open Lean

/-! ### The list-helper traversals are `map`s (as for `shift`/`subst`).

These push `toBvar` through the nested `List` occurrences (`construct` args, `case`
alternatives, `fix` definitions), exactly as `shiftArgs_eq_map`/`substArgs_eq_map`
do for the substitution kit — the standard shape every structural induction over
`toBvar` needs. -/

theorem toBvarArgs_eq_map (x : FVarId) (lvl : Nat) (l : List LBTerm) :
    toBvarArgs x lvl l = l.map (toBvar x lvl) := by
  induction l with
  | nil => rfl
  | cons t rest ih => simp [toBvarArgs, ih]

theorem toBvarAlts_eq_map (x : FVarId) (lvl : Nat) (l : List (List BinderName × LBTerm)) :
    toBvarAlts x lvl l = l.map (fun a => (a.1, toBvar x (lvl + a.1.length) a.2)) := by
  induction l with
  | nil => rfl
  | cons a rest ih => obtain ⟨ns, b⟩ := a; simp [toBvarAlts, ih]

theorem toBvarDefs_eq_map (x : FVarId) (lvl : Nat) (l : List (@FixDef LBTerm)) :
    toBvarDefs x lvl l = l.map (fun fd => { fd with body := toBvar x lvl fd.body }) := by
  induction l with
  | nil => rfl
  | cons fd rest ih => simp [toBvarDefs, ih]

/-- `abstract` unfolds to `toBvar … 0`. -/
theorem abstract_eq (x : FVarId) (t : LBTerm) : abstract x t = toBvar x 0 t := rfl

/-! ### Occurrence predicate: `hasFVar`

`hasFVar x t` says the free variable `x` occurs (structurally) in `t`. It mirrors
**exactly** the recursion shape of `toBvar`/`toBvarArgs`/`toBvarAlts`/`toBvarDefs`:
the naive `∃ t ∈ args, hasFVar x t` clause is rejected by the termination checker
(the recursive occurrence hides behind `List.Mem`), so the per-list traversals get
dedicated mutually-recursive helpers, and the `_iff` lemmas below recover the
natural existential form for downstream users. -/

mutual
/-- Does the free variable `x` occur in `t`? -/
def hasFVar (x : FVarId) : LBTerm → Prop
  | .box => False
  | .bvar _ => False
  | .fvar y => y = x
  | .lambda _ body => hasFVar x body
  | .letIn _ val body => hasFVar x val ∨ hasFVar x body
  | .app a b => hasFVar x a ∨ hasFVar x b
  | .const _ => False
  | .construct _ _ args => hasFVarArgs x args
  | .case _ discr alts => hasFVar x discr ∨ hasFVarAlts x alts
  | .proj _ e => hasFVar x e
  | .fix defs _ => hasFVarDefs x defs
  | .prim _ => False

/-- `hasFVar` over a `construct` argument list (disjunction down the list). -/
def hasFVarArgs (x : FVarId) : List LBTerm → Prop
  | [] => False
  | t :: rest => hasFVar x t ∨ hasFVarArgs x rest

/-- `hasFVar` over `case` alternatives (occurrence in some branch body). -/
def hasFVarAlts (x : FVarId) : List (List BinderName × LBTerm) → Prop
  | [] => False
  | (_, b) :: rest => hasFVar x b ∨ hasFVarAlts x rest

/-- `hasFVar` over `fix` definitions (occurrence in some fixpoint body). -/
def hasFVarDefs (x : FVarId) : List (@FixDef LBTerm) → Prop
  | [] => False
  | fd :: rest => hasFVar x fd.body ∨ hasFVarDefs x rest
end

/-! Simp-friendly unfolding lemmas, one per `hasFVar` clause (each holds by `rfl`
since the mutual block compiles by structural recursion). -/

@[simp] theorem hasFVar_box (x : FVarId) : hasFVar x .box ↔ False := Iff.rfl
@[simp] theorem hasFVar_bvar (x : FVarId) (i : Nat) : hasFVar x (.bvar i) ↔ False := Iff.rfl
@[simp] theorem hasFVar_fvar (x y : FVarId) : hasFVar x (.fvar y) ↔ y = x := Iff.rfl
@[simp] theorem hasFVar_lambda (x : FVarId) (nm : BinderName) (body : LBTerm) :
    hasFVar x (.lambda nm body) ↔ hasFVar x body := Iff.rfl
@[simp] theorem hasFVar_letIn (x : FVarId) (nm : BinderName) (val body : LBTerm) :
    hasFVar x (.letIn nm val body) ↔ hasFVar x val ∨ hasFVar x body := Iff.rfl
@[simp] theorem hasFVar_app (x : FVarId) (a b : LBTerm) :
    hasFVar x (.app a b) ↔ hasFVar x a ∨ hasFVar x b := Iff.rfl
@[simp] theorem hasFVar_const (x : FVarId) (kn : Kername) :
    hasFVar x (.const kn) ↔ False := Iff.rfl
@[simp] theorem hasFVar_construct (x : FVarId) (indid : InductiveId) (k : Nat)
    (args : List LBTerm) :
    hasFVar x (.construct indid k args) ↔ hasFVarArgs x args := Iff.rfl
@[simp] theorem hasFVar_case (x : FVarId) (info : InductiveId × Nat) (discr : LBTerm)
    (alts : List (List BinderName × LBTerm)) :
    hasFVar x (.case info discr alts) ↔ hasFVar x discr ∨ hasFVarAlts x alts := Iff.rfl
@[simp] theorem hasFVar_proj (x : FVarId) (pinfo : ProjectionInfo) (e : LBTerm) :
    hasFVar x (.proj pinfo e) ↔ hasFVar x e := Iff.rfl
@[simp] theorem hasFVar_fix (x : FVarId) (defs : List (@FixDef LBTerm)) (i : Nat) :
    hasFVar x (.fix defs i) ↔ hasFVarDefs x defs := Iff.rfl
@[simp] theorem hasFVar_prim (x : FVarId) (p : PrimVal) : hasFVar x (.prim p) ↔ False := Iff.rfl

/-! The list helpers in their natural existential form. -/

/-- `hasFVarArgs` is "some argument contains `x`". -/
theorem hasFVarArgs_iff (x : FVarId) (l : List LBTerm) :
    hasFVarArgs x l ↔ ∃ t ∈ l, hasFVar x t := by
  induction l with
  | nil => simp [hasFVarArgs]
  | cons t rest ih => simp [hasFVarArgs, ih]

/-- `hasFVarAlts` is "some branch body contains `x`". -/
theorem hasFVarAlts_iff (x : FVarId) (l : List (List BinderName × LBTerm)) :
    hasFVarAlts x l ↔ ∃ a ∈ l, hasFVar x a.2 := by
  induction l with
  | nil => simp [hasFVarAlts]
  | cons a rest ih => obtain ⟨ns, b⟩ := a; simp [hasFVarAlts, ih]

/-- `hasFVarDefs` is "some fixpoint body contains `x`". -/
theorem hasFVarDefs_iff (x : FVarId) (l : List (@FixDef LBTerm)) :
    hasFVarDefs x l ↔ ∃ d ∈ l, hasFVar x d.body := by
  induction l with
  | nil => simp [hasFVarDefs]
  | cons fd rest ih => simp [hasFVarDefs, ih]

/-- Bridge between `toBvar`'s Boolean `y == x` test and `hasFVar`'s propositional
`y = x` clause: `FVarId`'s derived `BEq` is definitionally `Name.beq` on the
underlying names, but core ships no `LawfulBEq FVarId` instance, so we prove the
reflection locally from `Name.beq_iff_eq`. -/
theorem fvarId_beq_iff_eq {x y : FVarId} : (x == y) = true ↔ x = y := by
  rw [show (x == y) = (x.name == y.name) from rfl, Name.beq_iff_eq]
  cases x
  cases y
  simp

/-! ### The no-op lemma: `toBvar` is the identity when the variable does not occur

The key foundation lemma: closing over a variable that does not occur does
nothing. In the `visitExpr` bridge this is what makes the `abstract x` step
vanish on subterms that never mention the freshly-opened `x` (e.g. erased/boxed
positions). Proved simultaneously with its three list-helper versions, by the
same mutual structural recursion as `toBvar` itself (this is exactly what
de-partializing `toBvar` bought us). -/

mutual
theorem toBvar_eq_of_not_hasFVar (x : FVarId) (lvl : Nat) :
    ∀ (t : LBTerm), ¬ hasFVar x t → toBvar x lvl t = t
  | .box, _ => rfl
  | .bvar _, _ => rfl
  | .fvar y, h => by
    simp only [hasFVar_fvar] at h
    simp [toBvar, fvarId_beq_iff_eq, h]
  | .lambda nm body, h => by
    simp only [hasFVar_lambda] at h
    simp only [toBvar, toBvar_eq_of_not_hasFVar x (lvl + 1) body h]
  | .letIn nm val body, h => by
    simp only [hasFVar_letIn, not_or] at h
    simp only [toBvar, toBvar_eq_of_not_hasFVar x lvl val h.1,
      toBvar_eq_of_not_hasFVar x (lvl + 1) body h.2]
  | .app a b, h => by
    simp only [hasFVar_app, not_or] at h
    simp only [toBvar, toBvar_eq_of_not_hasFVar x lvl a h.1,
      toBvar_eq_of_not_hasFVar x lvl b h.2]
  | .const _, _ => rfl
  | .construct indid k args, h => by
    simp only [hasFVar_construct] at h
    simp only [toBvar, toBvarArgs_eq_of_not_hasFVarArgs x lvl args h]
  | .case (indid, np) discr alts, h => by
    simp only [hasFVar_case, not_or] at h
    simp only [toBvar, toBvar_eq_of_not_hasFVar x lvl discr h.1,
      toBvarAlts_eq_of_not_hasFVarAlts x lvl alts h.2]
  | .proj pinfo e, h => by
    simp only [hasFVar_proj] at h
    simp only [toBvar, toBvar_eq_of_not_hasFVar x lvl e h]
  | .fix defs i, h => by
    simp only [hasFVar_fix] at h
    simp only [toBvar, toBvarDefs_eq_of_not_hasFVarDefs x (lvl + defs.length) defs h]
  | .prim _, _ => rfl

theorem toBvarArgs_eq_of_not_hasFVarArgs (x : FVarId) (lvl : Nat) :
    ∀ (l : List LBTerm), ¬ hasFVarArgs x l → toBvarArgs x lvl l = l
  | [], _ => rfl
  | t :: rest, h => by
    simp only [hasFVarArgs, not_or] at h
    simp only [toBvarArgs, toBvar_eq_of_not_hasFVar x lvl t h.1,
      toBvarArgs_eq_of_not_hasFVarArgs x lvl rest h.2]

theorem toBvarAlts_eq_of_not_hasFVarAlts (x : FVarId) (lvl : Nat) :
    ∀ (l : List (List BinderName × LBTerm)), ¬ hasFVarAlts x l → toBvarAlts x lvl l = l
  | [], _ => rfl
  | (ns, b) :: rest, h => by
    simp only [hasFVarAlts, not_or] at h
    simp only [toBvarAlts, toBvar_eq_of_not_hasFVar x (lvl + ns.length) b h.1,
      toBvarAlts_eq_of_not_hasFVarAlts x lvl rest h.2]

theorem toBvarDefs_eq_of_not_hasFVarDefs (x : FVarId) (lvl : Nat) :
    ∀ (l : List (@FixDef LBTerm)), ¬ hasFVarDefs x l → toBvarDefs x lvl l = l
  | [], _ => rfl
  | fd :: rest, h => by
    simp only [hasFVarDefs, not_or] at h
    simp only [toBvarDefs, toBvar_eq_of_not_hasFVar x lvl fd.body h.1,
      toBvarDefs_eq_of_not_hasFVarDefs x lvl rest h.2]
end

/-- `abstract` no-op corollary, in the form the `visitExpr` bridge consumes
(Erasure.lean's `abstract x (…)` steps at the top level of a binder body). -/
theorem abstract_eq_of_not_hasFVar (x : FVarId) (t : LBTerm) (h : ¬ hasFVar x t) :
    abstract x t = t :=
  toBvar_eq_of_not_hasFVar x 0 t h

/-! ### Positive sanity layer (non-vacuity checks)

`hasFVar` is inhabited where it should be, empty where it should be, and the
no-op lemma fires on concrete terms — both with abstract distinct variables and
with literal `FVarId`s. -/

example (x : FVarId) : hasFVar x (.fvar x) := by simp
example (x y : FVarId) (h : y ≠ x) : ¬ hasFVar x (.fvar y) := by simp [h]
example (x : FVarId) : ¬ hasFVar x .box := by simp
example (x : FVarId) : hasFVar x (.lambda .anon (.app .box (.fvar x))) := by simp
example : hasFVar ⟨`a⟩ (.app (.fvar ⟨`b⟩) (.fvar ⟨`a⟩)) := by simp
example : ¬ hasFVar ⟨`a⟩ (.app (.fvar ⟨`b⟩) .box) := by simp

example (x y : FVarId) (h : y ≠ x) :
    toBvar x 0 (.app (.fvar y) .box) = .app (.fvar y) .box :=
  toBvar_eq_of_not_hasFVar x 0 _ (by simp [h])
example :
    toBvar ⟨`a⟩ 0 (.app (.fvar ⟨`b⟩) .box) = .app (.fvar ⟨`b⟩) .box :=
  toBvar_eq_of_not_hasFVar _ 0 _ (by simp)
/- ... and, conversely, `toBvar` is *not* a no-op when the variable does occur. -/
example : toBvar ⟨`a⟩ 0 (.fvar ⟨`a⟩) = .bvar 0 := rfl

/-! ### Length preservation (cutoff bookkeeping for the `fix` cases below) -/

/-- `toBvarDefs` preserves length. -/
theorem toBvarDefs_length (x : FVarId) (lvl : Nat) (l : List (@FixDef LBTerm)) :
    (toBvarDefs x lvl l).length = l.length := by
  simp [toBvarDefs_eq_map]

/-- `LBTerm.shiftDefs` preserves length. (Its `_eq_map` sibling lives in
`Optimize.lean`, which this foundation file deliberately does not import, so we
prove the length fact directly.) -/
theorem shiftDefs_length (d c : Nat) (l : List (@FixDef LBTerm)) :
    (LBTerm.shiftDefs d c l).length = l.length := by
  induction l with
  | nil => rfl
  | cons fd rest ih => simp [LBTerm.shiftDefs, ih]

/-! ### Commutation with the de Bruijn kit: `toBvar` vs `LBTerm.shift`

`toBvar x lvl` inserts the de Bruijn index `lvl` (bumped under binders) and
never rewrites existing indices; `shift d c` bumps indices `≥ c` and ignores
`fvar`s. So as long as the insertion point sits at or above the cutoff
(`c ≤ lvl` — the configuration the bridge encounters: abstraction happens at the
level of the opened binder, shifts happen below it), the two commute, with the
insertion level moving by `d` on the shifted side. The statement was
sanity-checked on concrete instances (see the `rfl` examples below) before being
proved. -/

mutual
theorem toBvar_shift (x : FVarId) (d c lvl : Nat) (h : c ≤ lvl) :
    ∀ (t : LBTerm),
      LBTerm.shift d c (toBvar x lvl t) = toBvar x (lvl + d) (LBTerm.shift d c t)
  | .box => rfl
  | .bvar i => by
    by_cases hic : i ≥ c <;> simp [toBvar, LBTerm.shift, hic]
  | .fvar y => by
    -- split on the Boolean test itself (`FVarId` has no `Decidable` equality),
    -- keeping the proof constructive.
    cases hyx : (y == x)
    · simp [toBvar, LBTerm.shift, hyx]
    · simp [toBvar, LBTerm.shift, hyx, h]
  | .lambda nm body => by
    have ih := toBvar_shift x d (c + 1) (lvl + 1) (Nat.add_le_add_right h 1) body
    rw [Nat.add_right_comm] at ih
    simp only [toBvar, LBTerm.shift, ih]
  | .letIn nm val body => by
    have ihb := toBvar_shift x d (c + 1) (lvl + 1) (Nat.add_le_add_right h 1) body
    rw [Nat.add_right_comm] at ihb
    simp only [toBvar, LBTerm.shift, toBvar_shift x d c lvl h val, ihb]
  | .app a b => by
    simp only [toBvar, LBTerm.shift, toBvar_shift x d c lvl h a, toBvar_shift x d c lvl h b]
  | .const _ => rfl
  | .construct indid k args => by
    simp only [toBvar, LBTerm.shift, toBvarArgs_shiftArgs x d c lvl h args]
  | .case (indid, np) discr alts => by
    simp only [toBvar, LBTerm.shift, toBvar_shift x d c lvl h discr,
      toBvarAlts_shiftAlts x d c lvl h alts]
  | .proj pinfo e => by
    simp only [toBvar, LBTerm.shift, toBvar_shift x d c lvl h e]
  | .fix defs i => by
    have ih := toBvarDefs_shiftDefs x d (c + defs.length) (lvl + defs.length)
      (Nat.add_le_add_right h defs.length) defs
    rw [Nat.add_right_comm] at ih
    simp only [toBvar, LBTerm.shift, toBvarDefs_length, shiftDefs_length, ih]
  | .prim _ => rfl

theorem toBvarArgs_shiftArgs (x : FVarId) (d c lvl : Nat) (h : c ≤ lvl) :
    ∀ (l : List LBTerm),
      LBTerm.shiftArgs d c (toBvarArgs x lvl l) = toBvarArgs x (lvl + d) (LBTerm.shiftArgs d c l)
  | [] => rfl
  | t :: rest => by
    simp only [toBvarArgs, LBTerm.shiftArgs, toBvar_shift x d c lvl h t,
      toBvarArgs_shiftArgs x d c lvl h rest]

theorem toBvarAlts_shiftAlts (x : FVarId) (d c lvl : Nat) (h : c ≤ lvl) :
    ∀ (l : List (List BinderName × LBTerm)),
      LBTerm.shiftAlts d c (toBvarAlts x lvl l) = toBvarAlts x (lvl + d) (LBTerm.shiftAlts d c l)
  | [] => rfl
  | (ns, b) :: rest => by
    have ihb := toBvar_shift x d (c + ns.length) (lvl + ns.length)
      (Nat.add_le_add_right h ns.length) b
    rw [Nat.add_right_comm] at ihb
    simp only [toBvarAlts, LBTerm.shiftAlts, ihb, toBvarAlts_shiftAlts x d c lvl h rest]

theorem toBvarDefs_shiftDefs (x : FVarId) (d c lvl : Nat) (h : c ≤ lvl) :
    ∀ (l : List (@FixDef LBTerm)),
      LBTerm.shiftDefs d c (toBvarDefs x lvl l) = toBvarDefs x (lvl + d) (LBTerm.shiftDefs d c l)
  | [] => rfl
  | fd :: rest => by
    simp only [toBvarDefs, LBTerm.shiftDefs, toBvar_shift x d c lvl h fd.body,
      toBvarDefs_shiftDefs x d c lvl h rest]
end

/- Sanity: the `toBvar_shift` statement shape, checked by computation on a
concrete instance that crosses a binder (`d := 1`, `c := 0`, `lvl := 0`). -/
example :
    LBTerm.shift 1 0 (toBvar ⟨`a⟩ 0 (.lambda .anon (.app (.fvar ⟨`a⟩) (.bvar 0)))) =
      toBvar ⟨`a⟩ (0 + 1) (LBTerm.shift 1 0 (.lambda .anon (.app (.fvar ⟨`a⟩) (.bvar 0)))) := rfl

/-! ### Two abstractions at distinct variables commute

`toBvar` never rewrites existing `bvar`s, so closing `x` and closing `y ≠ x` are
completely independent: they commute with **no** index adjustment at all. This is
the reordering lemma for bridge cases that open several fvars at once (`fix`
blocks, iterated lambdas) and abstract them in sequence. -/

mutual
theorem toBvar_toBvar (x y : FVarId) (hxy : x ≠ y) (m n : Nat) :
    ∀ (t : LBTerm), toBvar y m (toBvar x n t) = toBvar x n (toBvar y m t)
  | .box => rfl
  | .bvar _ => rfl
  | .fvar z => by
    -- split on the Boolean tests themselves (`FVarId` has no `Decidable`
    -- equality), keeping the proof constructive; `z == x` and `z == y` cannot
    -- both hold since `x ≠ y`.
    cases hzx : (z == x) <;> cases hzy : (z == y)
    · simp [toBvar, hzx, hzy]
    · simp [toBvar, hzx, hzy]
    · simp [toBvar, hzx, hzy]
    · exact absurd ((fvarId_beq_iff_eq.mp hzx).symm.trans (fvarId_beq_iff_eq.mp hzy)) hxy
  | .lambda nm body => by
    simp only [toBvar, toBvar_toBvar x y hxy (m + 1) (n + 1) body]
  | .letIn nm val body => by
    simp only [toBvar, toBvar_toBvar x y hxy m n val, toBvar_toBvar x y hxy (m + 1) (n + 1) body]
  | .app a b => by
    simp only [toBvar, toBvar_toBvar x y hxy m n a, toBvar_toBvar x y hxy m n b]
  | .const _ => rfl
  | .construct indid k args => by
    simp only [toBvar, toBvarArgs_toBvarArgs x y hxy m n args]
  | .case (indid, np) discr alts => by
    simp only [toBvar, toBvar_toBvar x y hxy m n discr, toBvarAlts_toBvarAlts x y hxy m n alts]
  | .proj pinfo e => by
    simp only [toBvar, toBvar_toBvar x y hxy m n e]
  | .fix defs i => by
    simp only [toBvar, toBvarDefs_length,
      toBvarDefs_toBvarDefs x y hxy (m + defs.length) (n + defs.length) defs]
  | .prim _ => rfl

theorem toBvarArgs_toBvarArgs (x y : FVarId) (hxy : x ≠ y) (m n : Nat) :
    ∀ (l : List LBTerm), toBvarArgs y m (toBvarArgs x n l) = toBvarArgs x n (toBvarArgs y m l)
  | [] => rfl
  | t :: rest => by
    simp only [toBvarArgs, toBvar_toBvar x y hxy m n t, toBvarArgs_toBvarArgs x y hxy m n rest]

theorem toBvarAlts_toBvarAlts (x y : FVarId) (hxy : x ≠ y) (m n : Nat) :
    ∀ (l : List (List BinderName × LBTerm)),
      toBvarAlts y m (toBvarAlts x n l) = toBvarAlts x n (toBvarAlts y m l)
  | [] => rfl
  | (ns, b) :: rest => by
    simp only [toBvarAlts, toBvar_toBvar x y hxy (m + ns.length) (n + ns.length) b,
      toBvarAlts_toBvarAlts x y hxy m n rest]

theorem toBvarDefs_toBvarDefs (x y : FVarId) (hxy : x ≠ y) (m n : Nat) :
    ∀ (l : List (@FixDef LBTerm)),
      toBvarDefs y m (toBvarDefs x n l) = toBvarDefs x n (toBvarDefs y m l)
  | [] => rfl
  | fd :: rest => by
    simp only [toBvarDefs, toBvar_toBvar x y hxy m n fd.body,
      toBvarDefs_toBvarDefs x y hxy m n rest]
end

/- Sanity: the swap on a concrete term containing both variables. -/
example :
    toBvar ⟨`b⟩ 5 (toBvar ⟨`a⟩ 0 (.app (.fvar ⟨`a⟩) (.fvar ⟨`b⟩))) =
      toBvar ⟨`a⟩ 0 (toBvar ⟨`b⟩ 5 (.app (.fvar ⟨`a⟩) (.fvar ⟨`b⟩))) := rfl

/-!
Next (deferred — the remaining foundation): the `toBvar`↔`LBTerm.subst`
commutation (only needed once the bridge substitutes under abstractions), and the
binder-case simulation relating `abstract x (eraseCore (e.instantiate1' (.fvar x)))`
to `eraseCore e`. That simulation — together with lean4lean's `TrExprS.inst_fvar`
(fvar-opening ↔ `VLCtx` extension) — is the crux of the `fvar`↔de-Bruijn bridge,
and is a substantial (HIGH-difficulty) effort in its own right.
-/

end LeanToLambdaBox
