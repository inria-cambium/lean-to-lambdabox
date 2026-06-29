/-
# Task B — The `optimize` pass (MetaCoq §7.4)

The case-on-`Prop` expansion pass over target λ□ terms, proven to preserve
evaluation. Pure target-side reasoning (no lean4lean) → theorems must be
`sorryAx`-free. See the paper `3706056.pdf` §7.4 (`optimize`, `optimize_correct`).
-/
import LeanToLambdaBox.Basic
import LeanToLambdaBox.Semantics
import LeanToLambdaBox.Eval

namespace LeanToLambdaBox

open Lean

/-! ## B1 — the `optimize` pass -/

/-- Is the inductive `iid` propositional? Lookup chain:
    `envLookup Γ iid.mutualBlockName` → `some (.inductiveDecl body)` →
    `body.bodies[iid.idx]?` → `OneInductiveBody.propositional`. -/
def isPropositionalInductive (Γ : GlobalDeclarations) (iid : InductiveId) : Bool :=
  match LBTerm.envLookup Γ iid.mutualBlockName with
  | some (.inductiveDecl body) =>
    match body.bodies[iid.idx]? with
    | some oib => oib.propositional
    | none => false
  | _ => false

/-- Decide whether an (already-optimized) case collapses: a propositional,
    single-branch case becomes the branch body with `|names|` boxes substituted
    for the field binders; otherwise it stays a `.case`. Non-recursive so it can
    sit outside the `mutual` block. -/
def caseCollapse (info : InductiveId × Nat) (isProp : Bool)
    (discr' : LBTerm) (alts' : List (List BinderName × LBTerm)) : LBTerm :=
  match isProp, alts' with
  | true, [(names, body')] =>
    LBTerm.substList (List.replicate names.length .box) body'
  | _, _ => .case info discr' alts'

/- The `optimize` pass: structural identity except on a propositional,
    single-branch `.case`, which collapses to the branch body with `|names|`
    boxes substituted for the field binders.

    Factored through explicit list helpers (mirroring `Semantics.subst`) so the
    structural-recursion checker can see through the nested `List` occurrences. -/
mutual
def LBOptimize (Γ : GlobalDeclarations) : LBTerm → LBTerm
  | .box => .box
  | .bvar i => .bvar i
  | .fvar x => .fvar x
  | .lambda n b => .lambda n (LBOptimize Γ b)
  | .letIn n v b => .letIn n (LBOptimize Γ v) (LBOptimize Γ b)
  | .app f a => .app (LBOptimize Γ f) (LBOptimize Γ a)
  | .const kn => .const kn
  | .construct iid k args => .construct iid k (LBOptimizeArgs Γ args)
  | .case (iid, np) discr alts =>
    caseCollapse (iid, np) (isPropositionalInductive Γ iid)
      (LBOptimize Γ discr) (LBOptimizeAlts Γ alts)
  | .proj p e => .proj p (LBOptimize Γ e)
  | .fix defs i => .fix (LBOptimizeDefs Γ defs) i
  | .prim p => .prim p

def LBOptimizeArgs (Γ : GlobalDeclarations) : List LBTerm → List LBTerm
  | [] => []
  | t :: rest => LBOptimize Γ t :: LBOptimizeArgs Γ rest

def LBOptimizeAlts (Γ : GlobalDeclarations) :
    List (List BinderName × LBTerm) → List (List BinderName × LBTerm)
  | [] => []
  | (ns, b) :: rest => (ns, LBOptimize Γ b) :: LBOptimizeAlts Γ rest

def LBOptimizeDefs (Γ : GlobalDeclarations) :
    List (@FixDef LBTerm) → List (@FixDef LBTerm)
  | [] => []
  | fd :: rest => { fd with body := LBOptimize Γ fd.body } :: LBOptimizeDefs Γ rest
end

/-- Apply `LBOptimize` to every constant body in the environment. -/
def LBOptimize_env (Γ : GlobalDeclarations) : GlobalDeclarations :=
  Γ.map fun (kn, d) =>
    match d with
    | .constantDecl ⟨some body⟩ => (kn, .constantDecl ⟨some (LBOptimize Γ body)⟩)
    | _ => (kn, d)

/-! ### `subst` / `shift` list-helper equations (re-proved locally). -/

theorem substArgs_eq_map (s : LBTerm) (d : Nat) (l : List LBTerm) :
    LBTerm.substArgs s d l = l.map (LBTerm.subst s d) := by
  induction l with
  | nil => rfl
  | cons t rest ih => simp [LBTerm.substArgs, ih]

theorem substAlts_eq_map (s : LBTerm) (d : Nat) (l : List (List BinderName × LBTerm)) :
    LBTerm.substAlts s d l = l.map (fun a => (a.1, LBTerm.subst s (d + a.1.length) a.2)) := by
  induction l with
  | nil => rfl
  | cons a rest ih => obtain ⟨ns, b⟩ := a; simp [LBTerm.substAlts, ih]

/-! ### A usable structural induction principle for `LBTerm`.

`LBTerm` is a *nested* inductive (lists of subterms inside `construct`/`case`/
`fix`), so `induction t` is rejected. We build an eliminator whose list-carrying
constructors hand back a per-element induction hypothesis `∀ x ∈ l, P x`. -/

@[elab_as_elim]
def LBTerm.rec'
    {P : LBTerm → Prop}
    (hbox : P .box)
    (hbvar : ∀ i, P (.bvar i))
    (hfvar : ∀ x, P (.fvar x))
    (hlam : ∀ n b, P b → P (.lambda n b))
    (hletIn : ∀ n v b, P v → P b → P (.letIn n v b))
    (happ : ∀ f a, P f → P a → P (.app f a))
    (hconst : ∀ kn, P (.const kn))
    (hconstruct : ∀ iid k args, (∀ x ∈ args, P x) → P (.construct iid k args))
    (hcase : ∀ info discr alts, P discr → (∀ a ∈ alts, P a.2) → P (.case info discr alts))
    (hproj : ∀ p e, P e → P (.proj p e))
    (hfix : ∀ defs i, (∀ d ∈ defs, P d.body) → P (.fix defs i))
    (hprim : ∀ p, P (.prim p)) :
    ∀ t, P t := by
  refine fun t => LBTerm.rec
    (motive_1 := P)
    (motive_2 := fun l => ∀ x ∈ l, P x)
    (motive_3 := fun l => ∀ a ∈ l, P a.2)
    (motive_4 := fun l => ∀ d ∈ l, P d.body)
    (motive_5 := fun (a : List BinderName × LBTerm) => P a.2)
    (motive_6 := fun (d : @FixDef LBTerm) => P d.body)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t
  case _ => exact hbox
  case _ => exact hbvar
  case _ => exact hfvar
  case _ => exact fun n b ih => hlam n b ih
  case _ => exact fun n v b ihv ihb => hletIn n v b ihv ihb
  case _ => exact fun f a ihf iha => happ f a ihf iha
  case _ => exact hconst
  case _ => exact fun iid k args ih => hconstruct iid k args ih
  case _ => exact fun info discr alts ihd iha => hcase info discr alts ihd iha
  case _ => exact fun p e ih => hproj p e ih
  case _ => exact fun defs i ih => hfix defs i ih
  case _ => exact hprim
  case _ => exact List.forall_mem_nil _
  case _ => exact fun t l iht ihl => List.forall_mem_cons.mpr ⟨iht, ihl⟩
  case _ => exact List.forall_mem_nil _
  case _ => exact fun a l iha ihl => List.forall_mem_cons.mpr ⟨iha, ihl⟩
  case _ => exact List.forall_mem_nil _
  case _ => exact fun d l ihd ihl => List.forall_mem_cons.mpr ⟨ihd, ihl⟩
  case _ => exact fun _ snd ih => ih
  case _ => exact fun _ _ _ ih => ih

/-! ### Box is closed: substitution/shift act trivially on it. -/

@[simp] theorem shift_box (d c : Nat) : LBTerm.shift d c .box = .box := rfl
@[simp] theorem subst_box (s : LBTerm) (d : Nat) : LBTerm.subst s d .box = .box := rfl

/-! ### The single box-substitution swap.

We only ever substitute the closed term `.box`, which lets the generic
`subst`-`subst` commutation collapse (no shift bookkeeping on the substituee).
The statement is: substituting a `.box` at depth 0 commutes past an outer
substitution `subst s' (k+1)`, lowering it to `subst s' k`. -/

/-- `shift` list-helper as a `map`. -/
theorem shiftArgs_eq_map (d c : Nat) (l : List LBTerm) :
    LBTerm.shiftArgs d c l = l.map (LBTerm.shift d c) := by
  induction l with
  | nil => rfl
  | cons t rest ih => simp [LBTerm.shiftArgs, ih]

theorem shiftAlts_eq_map (d c : Nat) (l : List (List BinderName × LBTerm)) :
    LBTerm.shiftAlts d c l = l.map (fun a => (a.1, LBTerm.shift d (c + a.1.length) a.2)) := by
  induction l with
  | nil => rfl
  | cons a rest ih => obtain ⟨ns, b⟩ := a; simp [LBTerm.shiftAlts, ih]

theorem shiftDefs_eq_map (d c : Nat) (l : List (@FixDef LBTerm)) :
    LBTerm.shiftDefs d c l = l.map (fun fd => { fd with body := LBTerm.shift d c fd.body }) := by
  induction l with
  | nil => rfl
  | cons fd rest ih => simp [LBTerm.shiftDefs, ih]

theorem substDefs_eq_map (s : LBTerm) (d : Nat) (l : List (@FixDef LBTerm)) :
    LBTerm.substDefs s d l = l.map (fun fd => { fd with body := LBTerm.subst s d fd.body }) := by
  induction l with
  | nil => rfl
  | cons fd rest ih => simp [LBTerm.substDefs, ih]

/-- Substituting *anything* at depth `d` into a term shifted by `n+1` at cutoff
    `c` lowers the shift to `n`, provided the subst depth `d` lies in the shifted
    band `c ≤ d ≤ c + n` (so no shifted variable lands exactly on `d`). -/
theorem subst_shift_cancel (x : LBTerm) (n : Nat) :
    ∀ (c d : Nat), c ≤ d → d ≤ c + n → ∀ (s : LBTerm),
    LBTerm.subst x d (LBTerm.shift (n + 1) c s) = LBTerm.shift n c s := by
  intro c d hcd hdn s
  induction s using LBTerm.rec' generalizing c d with
  | hbox => rfl
  | hbvar i =>
    simp only [LBTerm.shift]
    split <;> rename_i h
    · -- i ≥ c : shifted to i+(n+1) > d, subst decrements to i+n
      simp only [LBTerm.subst]
      rw [if_neg (by omega), if_neg (by omega)]
      congr 1
    · -- i < c ≤ d : unshifted bvar i; subst leaves it
      simp only [LBTerm.subst]
      rw [if_pos (by omega)]
  | hfvar x => rfl
  | hconst kn => rfl
  | hprim p => rfl
  | hlam n' b ih =>
    simp only [LBTerm.shift, LBTerm.subst]; rw [ih (c + 1) (d + 1) (by omega) (by omega)]
  | hletIn n' v b ihv ihb =>
    simp only [LBTerm.shift, LBTerm.subst]
    rw [ihv c d hcd hdn, ihb (c + 1) (d + 1) (by omega) (by omega)]
  | happ f a ihf iha =>
    simp only [LBTerm.shift, LBTerm.subst]; rw [ihf c d hcd hdn, iha c d hcd hdn]
  | hproj p e ih => simp only [LBTerm.shift, LBTerm.subst]; rw [ih c d hcd hdn]
  | hconstruct iid k args ih =>
    simp only [LBTerm.shift, LBTerm.subst, shiftArgs_eq_map, substArgs_eq_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha; simp only [Function.comp]; exact ih a ha c d hcd hdn
  | hcase info discr alts ihd iha =>
    simp only [LBTerm.shift, LBTerm.subst, shiftAlts_eq_map, substAlts_eq_map, List.map_map]
    rw [ihd c d hcd hdn]
    congr 1
    apply List.map_congr_left
    intro a ha
    simp only [Function.comp]
    rw [iha a ha (c + a.1.length) (d + a.1.length) (by omega) (by omega)]
  | hfix defs i ih =>
    simp only [LBTerm.shift, LBTerm.subst, shiftDefs_eq_map, substDefs_eq_map,
      List.map_map, List.length_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    simp only [Function.comp]
    have := ih a ha (c + defs.length) (d + defs.length) (by omega) (by omega)
    simp only [this]

/-- General single-`box` substitution swap: substituting `.box` at depth `d`
    commutes past an outer substitution at depth `d + j + 1`, lowering it to
    `d + j`. (`box` is closed, so no shift bookkeeping leaks through.) -/
theorem box_subst_swap_gen (s' : LBTerm) (d j : Nat) (t : LBTerm) :
    LBTerm.subst .box d (LBTerm.subst s' (d + j + 1) t)
      = LBTerm.subst s' (d + j) (LBTerm.subst .box d t) := by
  induction t using LBTerm.rec' generalizing d with
  | hbox => rfl
  | hfvar x => rfl
  | hconst kn => rfl
  | hprim p => rfl
  | hbvar i =>
    -- Resolve the inner substitution first (it lives at depth d+j+1).
    show LBTerm.subst .box d (LBTerm.subst s' (d + j + 1) (.bvar i))
       = LBTerm.subst s' (d + j) (LBTerm.subst .box d (.bvar i))
    have hsub : ∀ (c : LBTerm) (m p : Nat), LBTerm.subst c m (.bvar p)
        = if p < m then .bvar p else if p = m then LBTerm.shift m 0 c else .bvar (p - 1) := by
      intro c m p; simp only [LBTerm.subst]
    rcases Nat.lt_trichotomy i d with hi | hi | hi
    · -- i < d
      rw [hsub, if_pos (by omega), hsub .box d i, if_pos hi, hsub, if_pos (by omega)]
    · -- i = d
      subst hi
      rw [hsub, if_pos (by omega), hsub .box i i, if_neg (by omega), if_pos rfl, shift_box,
        subst_box]
    · -- i > d
      rw [hsub .box d i, if_neg (by omega), if_neg (by omega)]
      rcases Nat.lt_trichotomy i (d + j + 1) with hj | hj | hj
      · -- d < i < d+j+1
        rw [hsub, if_pos hj, hsub .box d i, if_neg (by omega), if_neg (by omega),
          hsub s' (d + j) (i - 1), if_pos (by omega)]
      · -- i = d+j+1
        subst hj
        rw [hsub, if_neg (by omega), if_pos rfl, hsub s' (d + j) (d + j + 1 - 1),
          if_neg (by omega), if_pos (by omega)]
        exact subst_shift_cancel .box (d + j) 0 d (by omega) (by omega) s'
      · -- i > d+j+1
        rw [hsub, if_neg (by omega), if_neg (by omega), hsub s' (d + j) (i - 1),
          if_neg (by omega), if_neg (by omega), hsub .box d (i - 1),
          if_neg (by omega), if_neg (by omega)]
  | hlam n b ih =>
    simp only [LBTerm.subst]; congr 1
    have := ih (d + 1)
    rwa [show d + 1 + j + 1 = d + j + 1 + 1 by omega,
      show d + 1 + j = d + j + 1 by omega] at this
  | hletIn n v b ihv ihb =>
    simp only [LBTerm.subst]; congr 1
    · exact ihv d
    · have := ihb (d + 1)
      rwa [show d + 1 + j + 1 = d + j + 1 + 1 by omega,
        show d + 1 + j = d + j + 1 by omega] at this
  | happ f a ihf iha =>
    simp only [LBTerm.subst]; congr 1
    · exact ihf d
    · exact iha d
  | hproj p e ih =>
    simp only [LBTerm.subst]; congr 1; exact ih d
  | hconstruct iid k args ih =>
    simp only [LBTerm.subst, substArgs_eq_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha; simp only [Function.comp]; exact ih a ha d
  | hcase info discr alts ihd iha =>
    simp only [LBTerm.subst, substAlts_eq_map, List.map_map]
    rw [ihd d]
    congr 1
    apply List.map_congr_left
    intro a ha; simp only [Function.comp]
    have := iha a ha (d + a.1.length)
    rw [show d + a.1.length + j + 1 = d + j + 1 + a.1.length by omega,
      show d + a.1.length + j = d + j + a.1.length by omega] at this
    rw [this]
  | hfix defs i ih =>
    simp only [LBTerm.subst, substDefs_eq_map, List.map_map, List.length_map]
    congr 1
    apply List.map_congr_left
    intro a ha; simp only [Function.comp]
    have := ih a ha (d + defs.length)
    rw [show d + defs.length + j + 1 = d + j + 1 + defs.length by omega,
      show d + defs.length + j = d + j + defs.length by omega] at this
    congr 1

/-- The specialised swap used by `LBOptimize_correct`: a `.box` at depth 0
    commutes past an outer substitution at depth `k+1`. -/
theorem box_subst_swap (s' : LBTerm) (k : Nat) (t : LBTerm) :
    LBTerm.subst .box 0 (LBTerm.subst s' (k + 1) t)
      = LBTerm.subst s' k (LBTerm.subst .box 0 t) := by
  have := box_subst_swap_gen s' 0 k t
  simpa using this

/-- `substList` of `n+1` boxes peels one box off the front. -/
theorem substList_replicate_box_succ (n : Nat) (u : LBTerm) :
    LBTerm.substList (List.replicate (n + 1) .box) u
      = LBTerm.substList (List.replicate n .box) (LBTerm.subst .box 0 u) := by
  simp only [LBTerm.substList, List.replicate_succ, List.foldl_cons, LBTerm.subst1]

/-- Iterated box-substitution commutes past an outer substitution, lowering its
    depth by the number of boxes. This is `box_subst_swap` lifted to `substList`
    of `n` boxes — the engine behind the `optimize`/`subst` commutation. -/
theorem substList_replicate_box_subst (s' : LBTerm) (n : Nat) :
    ∀ (d : Nat) (u : LBTerm),
    LBTerm.substList (List.replicate n .box) (LBTerm.subst s' (d + n) u)
      = LBTerm.subst s' d (LBTerm.substList (List.replicate n .box) u) := by
  induction n with
  | zero => intro d u; simp [LBTerm.substList]
  | succ n ih =>
    intro d u
    rw [substList_replicate_box_succ]
    rw [show d + (n + 1) = (d + n) + 1 by omega]
    rw [box_subst_swap s' (d + n) u]
    rw [ih d (LBTerm.subst .box 0 u), substList_replicate_box_succ]

/-! ### Structural equations for the list helpers (as `map`/`zip` forms). -/

theorem LBOptimizeArgs_eq_map (Γ : GlobalDeclarations) (l : List LBTerm) :
    LBOptimizeArgs Γ l = l.map (LBOptimize Γ) := by
  induction l with
  | nil => rfl
  | cons t rest ih => simp [LBOptimizeArgs, ih]

theorem LBOptimizeAlts_eq_map (Γ : GlobalDeclarations)
    (l : List (List BinderName × LBTerm)) :
    LBOptimizeAlts Γ l = l.map (fun a => (a.1, LBOptimize Γ a.2)) := by
  induction l with
  | nil => rfl
  | cons a rest ih => obtain ⟨ns, b⟩ := a; simp [LBOptimizeAlts, ih]

theorem LBOptimizeDefs_eq_map (Γ : GlobalDeclarations) (l : List (@FixDef LBTerm)) :
    LBOptimizeDefs Γ l = l.map (fun fd => { fd with body := LBOptimize Γ fd.body }) := by
  induction l with
  | nil => rfl
  | cons fd rest ih => simp [LBOptimizeDefs, ih]

/-! ### `LBOptimize` unfolding equations (used to drive `simp only`). -/

@[simp] theorem LBOptimize_box (Γ) : LBOptimize Γ .box = .box := rfl
@[simp] theorem LBOptimize_bvar (Γ i) : LBOptimize Γ (.bvar i) = .bvar i := rfl
@[simp] theorem LBOptimize_fvar (Γ x) : LBOptimize Γ (.fvar x) = .fvar x := rfl
@[simp] theorem LBOptimize_const (Γ kn) : LBOptimize Γ (.const kn) = .const kn := rfl
@[simp] theorem LBOptimize_prim (Γ p) : LBOptimize Γ (.prim p) = .prim p := rfl
@[simp] theorem LBOptimize_lambda (Γ n b) :
    LBOptimize Γ (.lambda n b) = .lambda n (LBOptimize Γ b) := rfl
@[simp] theorem LBOptimize_letIn (Γ n v b) :
    LBOptimize Γ (.letIn n v b) = .letIn n (LBOptimize Γ v) (LBOptimize Γ b) := rfl
@[simp] theorem LBOptimize_app (Γ f a) :
    LBOptimize Γ (.app f a) = .app (LBOptimize Γ f) (LBOptimize Γ a) := rfl
@[simp] theorem LBOptimize_proj (Γ p e) :
    LBOptimize Γ (.proj p e) = .proj p (LBOptimize Γ e) := rfl
@[simp] theorem LBOptimize_construct (Γ iid k args) :
    LBOptimize Γ (.construct iid k args) = .construct iid k (LBOptimizeArgs Γ args) := rfl
@[simp] theorem LBOptimize_fix (Γ defs i) :
    LBOptimize Γ (.fix defs i) = .fix (LBOptimizeDefs Γ defs) i := rfl
theorem LBOptimize_case (Γ iid np discr alts) :
    LBOptimize Γ (.case (iid, np) discr alts)
      = caseCollapse (iid, np) (isPropositionalInductive Γ iid)
          (LBOptimize Γ discr) (LBOptimizeAlts Γ alts) := rfl

/-! ### `caseCollapse` equation lemmas. -/

theorem caseCollapse_prop_single (info iid np) (names body') (h : info = (iid, np)) :
    caseCollapse info true discr' [(names, body')]
      = LBTerm.substList (List.replicate names.length .box) body' := by
  subst h; rfl

theorem caseCollapse_nil (info b discr') :
    caseCollapse info b discr' [] = .case info discr' [] := by
  cases b <;> rfl

theorem caseCollapse_cons2 (info b discr') (x y) (zs) :
    caseCollapse info b discr' (x :: y :: zs) = .case info discr' (x :: y :: zs) := by
  cases b <;> rfl

theorem caseCollapse_nonprop (info discr') (alts') :
    caseCollapse info false discr' alts' = .case info discr' alts' := rfl

/-! ### `LBOptimize` commutes with `shift` (needed for the `bvar = d` subst case). -/

/-- A `.box` substitution at depth `e` commutes past an outer `shift` with
    cutoff `c+1`, lowering the cutoff to `c`, provided `e ≤ c`. (`box` is closed.) -/
theorem box_subst_shift_swap (d : Nat) :
    ∀ (e c : Nat), e ≤ c → ∀ (u : LBTerm),
    LBTerm.subst .box e (LBTerm.shift d (c + 1) u)
      = LBTerm.shift d c (LBTerm.subst .box e u) := by
  intro e c hec u
  induction u using LBTerm.rec' generalizing e c with
  | hbox => rfl
  | hfvar x => rfl
  | hconst kn => rfl
  | hprim p => rfl
  | hbvar i =>
    have hsh : ∀ (m p : Nat), LBTerm.shift d m (.bvar p)
        = if p ≥ m then .bvar (p + d) else .bvar p := by
      intro m p; simp only [LBTerm.shift]
    have hsb : ∀ (m p : Nat), LBTerm.subst .box m (.bvar p)
        = if p < m then .bvar p else if p = m then .box else .bvar (p - 1) := by
      intro m p; simp only [LBTerm.subst, shift_box]
    by_cases hcut : i ≥ c + 1
    · -- shifted up by d
      rw [hsh, if_pos hcut]
      rw [hsb (e) (i + d), if_neg (by omega), if_neg (by omega)]
      rw [hsb e i, if_neg (by omega), if_neg (by omega)]
      rw [hsh c (i - 1), if_pos (by omega)]
      congr 1; omega
    · -- not shifted (i ≤ c)
      rw [hsh, if_neg hcut]
      by_cases he1 : i < e
      · rw [hsb e i, if_pos he1, hsh c i, if_neg (by omega)]
      · by_cases he2 : i = e
        · subst he2
          rw [hsb i i, if_neg (by omega), if_pos rfl, shift_box]
        · rw [hsb e i, if_neg (by omega), if_neg (by omega), hsh c (i - 1), if_neg (by omega)]
  | hlam n b ih =>
    simp only [LBTerm.shift, LBTerm.subst]; congr 1; exact ih (e + 1) (c + 1) (by omega)
  | hletIn n v b ihv ihb =>
    simp only [LBTerm.shift, LBTerm.subst]; congr 1
    · exact ihv e c hec
    · exact ihb (e + 1) (c + 1) (by omega)
  | happ f a ihf iha =>
    simp only [LBTerm.shift, LBTerm.subst]; congr 1
    · exact ihf e c hec
    · exact iha e c hec
  | hproj p e' ih => simp only [LBTerm.shift, LBTerm.subst]; congr 1; exact ih e c hec
  | hconstruct iid k args ih =>
    simp only [LBTerm.shift, LBTerm.subst, shiftArgs_eq_map, substArgs_eq_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha; simp only [Function.comp]; exact ih a ha e c hec
  | hcase info discr alts ihd iha =>
    simp only [LBTerm.shift, LBTerm.subst, shiftAlts_eq_map, substAlts_eq_map, List.map_map]
    rw [ihd e c hec]
    congr 1
    apply List.map_congr_left
    intro a ha; simp only [Function.comp]
    have := iha a ha (e + a.1.length) (c + a.1.length) (by omega)
    rw [show c + a.1.length + 1 = c + 1 + a.1.length by omega] at this
    rw [this]
  | hfix defs i ih =>
    simp only [LBTerm.shift, LBTerm.subst, shiftDefs_eq_map, substDefs_eq_map,
      List.map_map, List.length_map]
    congr 1
    apply List.map_congr_left
    intro a ha; simp only [Function.comp]
    have := ih a ha (e + defs.length) (c + defs.length) (by omega)
    rw [show c + defs.length + 1 = c + 1 + defs.length by omega] at this
    congr 1

/-- Iterated box-substitution commutes past an outer `shift`, lowering its
    cutoff by the number of boxes. -/
theorem substList_replicate_box_shift (d : Nat) (n : Nat) :
    ∀ (c : Nat) (u : LBTerm),
    LBTerm.substList (List.replicate n .box) (LBTerm.shift d (c + n) u)
      = LBTerm.shift d c (LBTerm.substList (List.replicate n .box) u) := by
  induction n with
  | zero => intro c u; simp [LBTerm.substList]
  | succ n ih =>
    intro c u
    rw [substList_replicate_box_succ, show c + (n + 1) = (c + n) + 1 by omega,
      box_subst_shift_swap d 0 (c + n) (by omega) u, ih c (LBTerm.subst .box 0 u),
      substList_replicate_box_succ]

/-- `caseCollapse` commutes with substitution: substituting into the collapsed
    term equals collapsing the substituted-into discriminant/branches. The only
    subtle case is the prop single-branch collapse, handled by
    `substList_replicate_box_subst` (the boxes are closed). -/
theorem caseCollapse_subst (info : InductiveId × Nat) (b : Bool) (s' : LBTerm) (d : Nat)
    (discr' : LBTerm) (alts' : List (List BinderName × LBTerm)) :
    LBTerm.subst s' d (caseCollapse info b discr' alts')
      = caseCollapse info b (LBTerm.subst s' d discr') (LBTerm.substAlts s' d alts') := by
  cases b with
  | false => simp only [caseCollapse_nonprop, LBTerm.subst]
  | true =>
    match alts' with
    | [] => simp only [LBTerm.substAlts, caseCollapse_nil, LBTerm.subst]
    | [(names, body')] =>
      obtain ⟨iid, np⟩ := info
      simp only [LBTerm.substAlts, caseCollapse_prop_single (iid, np) iid np _ _ rfl]
      exact (substList_replicate_box_subst s' names.length d body').symm
    | (x :: y :: zs) =>
      simp only [LBTerm.substAlts, caseCollapse_cons2, LBTerm.subst]

theorem caseCollapse_shift (info : InductiveId × Nat) (b : Bool) (d c : Nat)
    (discr' : LBTerm) (alts' : List (List BinderName × LBTerm)) :
    LBTerm.shift d c (caseCollapse info b discr' alts')
      = caseCollapse info b (LBTerm.shift d c discr') (LBTerm.shiftAlts d c alts') := by
  cases b with
  | false => simp only [caseCollapse_nonprop, LBTerm.shift]
  | true =>
    match alts' with
    | [] => simp only [LBTerm.shiftAlts, caseCollapse_nil, LBTerm.shift]
    | [(names, body')] =>
      obtain ⟨iid, np⟩ := info
      simp only [LBTerm.shiftAlts, caseCollapse_prop_single (iid, np) iid np _ _ rfl]
      exact (substList_replicate_box_shift d names.length c body').symm
    | (x :: y :: zs) =>
      simp only [LBTerm.shiftAlts, caseCollapse_cons2, LBTerm.shift]

/-- `LBOptimize` commutes with `shift`. -/
theorem LBOptimize_shift_comm (Γ : GlobalDeclarations) (d : Nat) :
    ∀ (c : Nat) (t : LBTerm),
    LBOptimize Γ (LBTerm.shift d c t) = LBTerm.shift d c (LBOptimize Γ t) := by
  intro c t
  induction t using LBTerm.rec' generalizing c with
  | hbox => rfl
  | hbvar i => simp only [LBTerm.shift, LBOptimize_bvar]; split <;> rfl
  | hfvar x => rfl
  | hconst kn => rfl
  | hprim p => rfl
  | hlam n b ih => simp only [LBTerm.shift, LBOptimize_lambda]; rw [ih (c + 1)]
  | hletIn n v b ihv ihb =>
    simp only [LBTerm.shift, LBOptimize_letIn]; rw [ihv c, ihb (c + 1)]
  | happ f a ihf iha => simp only [LBTerm.shift, LBOptimize_app]; rw [ihf c, iha c]
  | hproj p e ih => simp only [LBTerm.shift, LBOptimize_proj]; rw [ih c]
  | hconstruct iid k args ih =>
    simp only [LBTerm.shift, LBOptimize_construct, LBOptimizeArgs_eq_map,
      shiftArgs_eq_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha; simp only [Function.comp]; exact ih a ha c
  | hcase info discr alts ihd iha =>
    obtain ⟨iid, np⟩ := info
    rw [show LBTerm.shift d c (LBTerm.case (iid, np) discr alts)
          = LBTerm.case (iid, np) (LBTerm.shift d c discr) (LBTerm.shiftAlts d c alts) from rfl]
    rw [LBOptimize_case, LBOptimize_case, caseCollapse_shift, ihd c]
    -- remaining: the optimized-then-shifted alts agree both ways
    have halts : LBOptimizeAlts Γ (LBTerm.shiftAlts d c alts)
        = LBTerm.shiftAlts d c (LBOptimizeAlts Γ alts) := by
      rw [LBOptimizeAlts_eq_map, shiftAlts_eq_map, shiftAlts_eq_map, LBOptimizeAlts_eq_map,
        List.map_map, List.map_map]
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]
      exact Prod.ext rfl (iha a ha (c + a.1.length))
    rw [halts]
  | hfix defs i ih =>
    simp only [LBTerm.shift, LBOptimize_fix, LBOptimizeDefs_eq_map,
      shiftDefs_eq_map, List.map_map, List.length_map]
    congr 1
    apply List.map_congr_left
    intro a ha; simp only [Function.comp]
    have := ih a ha (c + defs.length)
    congr 1

/-! ## B3 (key lemma) — `LBOptimize` commutes with substitution.

The crux of Task B. The dangerous case is a propositional single-branch
`.case`, where `LBOptimize` *removes* binders (collapsing to the body with boxes
substituted). The collapse on the substituted term lines up with substituting
into the collapsed term precisely because the substituted-in boxes are closed —
this is exactly `substList_replicate_box_subst`. -/
theorem LBOptimize_subst_comm (Γ : GlobalDeclarations) (s : LBTerm) :
    ∀ (d : Nat) (t : LBTerm),
    LBOptimize Γ (LBTerm.subst s d t)
      = LBTerm.subst (LBOptimize Γ s) d (LBOptimize Γ t) := by
  intro d t
  induction t using LBTerm.rec' generalizing d with
  | hbox => rfl
  | hbvar i =>
    simp only [LBTerm.subst, LBOptimize_bvar]
    split
    · rfl
    · split
      · -- bvar = d : result is shift d 0 s; optimize and shift commute
        exact LBOptimize_shift_comm Γ d 0 s
      · rfl
  | hfvar x => rfl
  | hconst kn => rfl
  | hprim p => rfl
  | hlam n b ih =>
    simp only [LBTerm.subst, LBOptimize_lambda]; rw [ih (d + 1)]
  | hletIn n v b ihv ihb =>
    simp only [LBTerm.subst, LBOptimize_letIn]; rw [ihv d, ihb (d + 1)]
  | happ f a ihf iha =>
    simp only [LBTerm.subst, LBOptimize_app]; rw [ihf d, iha d]
  | hproj p e ih =>
    simp only [LBTerm.subst, LBOptimize_proj]; rw [ih d]
  | hconstruct iid k args ih =>
    simp only [LBTerm.subst, LBOptimize_construct, LBOptimizeArgs_eq_map,
      substArgs_eq_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha; simp only [Function.comp]; exact ih a ha d
  | hcase info discr alts ihd iha =>
    obtain ⟨iid, np⟩ := info
    -- subst pushes into discr/alts; optimize then collapses both sides identically.
    rw [show LBTerm.subst s d (LBTerm.case (iid, np) discr alts)
          = LBTerm.case (iid, np) (LBTerm.subst s d discr) (LBTerm.substAlts s d alts) from rfl]
    rw [LBOptimize_case, LBOptimize_case, caseCollapse_subst, ihd d]
    -- remaining: the optimized-then-substituted alts agree both ways
    have halts : LBOptimizeAlts Γ (LBTerm.substAlts s d alts)
        = LBTerm.substAlts (LBOptimize Γ s) d (LBOptimizeAlts Γ alts) := by
      rw [LBOptimizeAlts_eq_map, substAlts_eq_map, substAlts_eq_map, LBOptimizeAlts_eq_map,
        List.map_map, List.map_map]
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]
      exact Prod.ext rfl (iha a ha (d + a.1.length))
    rw [halts]
  | hfix defs i ih =>
    simp only [LBTerm.subst, LBOptimize_fix, LBOptimizeDefs_eq_map,
      substDefs_eq_map, List.map_map, List.length_map]
    congr 1
    apply List.map_congr_left
    intro a ha; simp only [Function.comp]
    have := ih a ha (d + defs.length)
    congr 1

/-- `LBOptimize` commutes with substituting a list of boxes (the form arising
    from a collapsed prop-case). Specialisation of `LBOptimize_subst_comm`. -/
theorem LBOptimize_substList_box (Γ : GlobalDeclarations) (n : Nat) (t : LBTerm) :
    LBOptimize Γ (LBTerm.substList (List.replicate n .box) t)
      = LBTerm.substList (List.replicate n .box) (LBOptimize Γ t) := by
  induction n generalizing t with
  | zero => simp [LBTerm.substList]
  | succ n ih =>
    rw [substList_replicate_box_succ, ih, LBOptimize_subst_comm Γ .box 0 t,
      LBOptimize_box, ← substList_replicate_box_succ]

/-- `LBOptimize` commutes with simultaneous substitution. General form of
    `LBOptimize_substList_box`. -/
theorem LBOptimize_substList (Γ : GlobalDeclarations) :
    ∀ (ss : List LBTerm) (t : LBTerm),
    LBOptimize Γ (LBTerm.substList ss t)
      = LBTerm.substList (ss.map (LBOptimize Γ)) (LBOptimize Γ t) := by
  intro ss
  induction ss with
  | nil => intro t; rfl
  | cons s rest ih =>
    intro t
    have hstep : LBTerm.substList (s :: rest) t
        = LBTerm.substList rest (LBTerm.subst1 s t) := by
      simp only [LBTerm.substList, List.foldl_cons]
    rw [hstep, ih (LBTerm.subst1 s t), LBTerm.subst1, LBOptimize_subst_comm Γ s 0 t]
    simp only [List.map_cons, LBTerm.substList, List.foldl_cons, LBTerm.subst1]

/-- Does `LBOptimize` collapse this case?  `true` exactly when the inductive is
    propositional *and* the branch list is a single branch. -/
def wouldCollapse (Γ : GlobalDeclarations) (iid : InductiveId)
    (alts : List (List BinderName × LBTerm)) : Bool :=
  isPropositionalInductive Γ iid &&
    (match alts with | [_] => true | _ => false)

/-! ## B2 — the flagged big-step relation `EvalProp`.

A faithful copy of `Eval` (all ten rules) **plus** the prop-case rule
`iota_box`: a propositional single-branch case whose discriminant evaluates to
`box` reduces by substituting boxes for the branch's field binders. This is
MetaCoq's prop-case rule that the `optimize` pass *removes*; our flag-less
`Eval` is exactly the `disable_prop_cases` semantics. -/
inductive EvalProp (Γ : GlobalDeclarations) : LBTerm → LBTerm → Prop
  | box : EvalProp Γ .box .box
  | lam (n : BinderName) (b : LBTerm) : EvalProp Γ (.lambda n b) (.lambda n b)
  | fvar (x : FVarId) : EvalProp Γ (.fvar x) (.fvar x)
  | prim (p : PrimVal) : EvalProp Γ (.prim p) (.prim p)
  | beta {f a : LBTerm} {n : BinderName} {b av r : LBTerm} :
      EvalProp Γ f (.lambda n b) → EvalProp Γ a av → EvalProp Γ (LBTerm.subst1 av b) r →
      EvalProp Γ (.app f a) r
  | app_box {f a : LBTerm} : EvalProp Γ f .box → EvalProp Γ (.app f a) .box
  | zeta {n : BinderName} {v b vv r : LBTerm} :
      EvalProp Γ v vv → EvalProp Γ (LBTerm.subst1 vv b) r → EvalProp Γ (.letIn n v b) r
  | delta {kn : Kername} {body r : LBTerm} :
      LBTerm.envLookup Γ kn = some (.constantDecl ⟨some body⟩) → EvalProp Γ body r →
      EvalProp Γ (.const kn) r
  | construct {iid : InductiveId} {k : Nat} {args vs : List LBTerm}
      (hl : args.length = vs.length)
      (hargs : ∀ i (h : i < args.length), EvalProp Γ args[i] (vs[i]'(hl ▸ h))) :
      EvalProp Γ (.construct iid k args) (.construct iid k vs)
  | iota {iid : InductiveId} {np k : Nat} {discr : LBTerm}
         {alts : List (List BinderName × LBTerm)} {cargs : List LBTerm}
         {names : List BinderName} {body r : LBTerm} :
      wouldCollapse Γ iid alts = false →
      EvalProp Γ discr (.construct iid k cargs) →
      alts[k]? = some (names, body) →
      EvalProp Γ (LBTerm.substList cargs body) r →
      EvalProp Γ (.case (iid, np) discr alts) r
  /-- The prop-case rule (`enable_prop_cases`): a single-branch case on a
      propositional inductive, whose discriminant evaluates to `box`, reduces by
      substituting `|names|` boxes for the field binders of its sole branch. -/
  | iota_box {iid : InductiveId} {np : Nat} {discr : LBTerm}
             {names : List BinderName} {body r : LBTerm} :
      isPropositionalInductive Γ iid = true →
      EvalProp Γ discr .box →
      EvalProp Γ (LBTerm.substList (List.replicate names.length .box) body) r →
      EvalProp Γ (.case (iid, np) discr [(names, body)]) r

/-! ### `LBOptimize_env` lookup compatibility. -/

/-- Auxiliary: the optimization map applied to a *list* `L` (with bodies
    optimized w.r.t. a fixed environment `Δ`) preserves constant lookups. -/
theorem envLookup_map_opt (Δ : GlobalDeclarations) :
    ∀ (L : GlobalDeclarations) {kn : Kername} {body : LBTerm},
    LBTerm.envLookup L kn = some (.constantDecl ⟨some body⟩) →
    LBTerm.envLookup (L.map fun (kn, d) =>
        match d with
        | .constantDecl ⟨some b⟩ => (kn, .constantDecl ⟨some (LBOptimize Δ b)⟩)
        | _ => (kn, d)) kn
      = some (.constantDecl ⟨some (LBOptimize Δ body)⟩) := by
  intro L
  induction L with
  | nil => intro kn body h; simp [LBTerm.envLookup] at h
  | cons hd rest ih =>
    intro kn body h
    obtain ⟨k, d⟩ := hd
    simp only [List.map_cons]
    unfold LBTerm.envLookup at h ⊢
    by_cases hk : k.id == kn.id
    · rw [if_pos hk] at h
      cases d with
      | constantDecl cb =>
        cases cb with
        | mk ob =>
          cases ob with
          | none => simp at h
          | some b =>
            injection h with h'; injection h' with h''
            obtain rfl : b = body := by injection h'' with hb; injection hb
            dsimp only
            rw [if_pos hk]
      | inductiveDecl b => simp at h
    · rw [if_neg hk] at h
      cases d with
      | constantDecl cb =>
        cases cb with
        | mk ob =>
          cases ob with
          | none => dsimp only; rw [if_neg hk]; exact ih h
          | some b => dsimp only; rw [if_neg hk]; exact ih h
      | inductiveDecl b => dsimp only; rw [if_neg hk]; exact ih h

/-- Looking up a constant body in the optimized environment yields the optimized
    body (optimized w.r.t. the *original* `Γ`, matching `LBOptimize_env`). -/
theorem envLookup_LBOptimize_env {Γ : GlobalDeclarations} {kn : Kername} {body : LBTerm}
    (h : LBTerm.envLookup Γ kn = some (.constantDecl ⟨some body⟩)) :
    LBTerm.envLookup (LBOptimize_env Γ) kn
      = some (.constantDecl ⟨some (LBOptimize Γ body)⟩) :=
  envLookup_map_opt Γ Γ h

/-! ### `LBOptimize` on a `.case`, split by whether it collapses. -/

theorem LBOptimize_case_noncollapse (Γ iid np discr alts)
    (h : wouldCollapse Γ iid alts = false) :
    LBOptimize Γ (.case (iid, np) discr alts)
      = .case (iid, np) (LBOptimize Γ discr) (LBOptimizeAlts Γ alts) := by
  rw [LBOptimize_case]
  unfold wouldCollapse at h
  rw [Bool.and_eq_false_iff] at h
  rcases h with hp | hs
  · rw [hp]; rfl
  · -- not a single branch
    cases alts with
    | nil => simp only [LBOptimizeAlts, caseCollapse_nil]
    | cons a rest =>
      cases rest with
      | nil => simp only [reduceCtorEq] at hs
      | cons a2 rest2 => simp only [LBOptimizeAlts, caseCollapse_cons2]

theorem LBOptimize_case_collapse (Γ iid np discr names body)
    (hp : isPropositionalInductive Γ iid = true) :
    LBOptimize Γ (.case (iid, np) discr [(names, body)])
      = LBTerm.substList (List.replicate names.length .box) (LBOptimize Γ body) := by
  rw [LBOptimize_case]
  simp only [LBOptimizeAlts]
  rw [hp, caseCollapse_prop_single (iid, np) iid np _ _ rfl]

/-! ## B3 — `LBOptimize_correct`.

`EvalProp` (prop-cases enabled) implies `Eval` on the optimized term in the
optimized environment. The crux is `iota_box`, discharged by
`LBOptimize_substList_box`; the regular `iota` is guarded by `wouldCollapse =
false`, so the optimized case stays a `.case` and reuses `Eval.iota`. -/
theorem LBOptimize_correct {Γ : GlobalDeclarations} {t v : LBTerm} :
    EvalProp Γ t v → Eval (LBOptimize_env Γ) (LBOptimize Γ t) (LBOptimize Γ v) := by
  intro h
  induction h with
  | box => exact .box
  | lam n b => exact .lam n (LBOptimize Γ b)
  | fvar x => exact .fvar x
  | prim p => exact .prim p
  | @beta f a n b av r _ _ _ ihf iha ihbody =>
    refine .beta (n := n) (b := LBOptimize Γ b) ?_ iha ?_
    · simpa using ihf
    · rw [LBTerm.subst1, LBOptimize_subst_comm Γ av 0 b] at ihbody
      exact ihbody
  | @app_box f a _ ihf => exact .app_box (by simpa using ihf)
  | @zeta n v b vv r _ _ ihv ihbody =>
    refine .zeta (vv := LBOptimize Γ vv) ihv ?_
    rw [LBTerm.subst1, LBOptimize_subst_comm Γ vv 0 b] at ihbody
    exact ihbody
  | @delta kn body r hlk _ ihbody =>
    exact .delta (envLookup_LBOptimize_env hlk) ihbody
  | @construct iid k args vs hl hargs ihargs =>
    simp only [LBOptimize_construct, LBOptimizeArgs_eq_map]
    refine .construct (by simp [hl]) (fun i hi => ?_)
    simp only [List.getElem_map]
    have hi' : i < args.length := by simpa using hi
    have := ihargs i hi'
    simpa using this
  | @iota iid np k discr alts cargs names body r hwc hdiscr hsel _ ihd ihbody =>
    rw [LBOptimize_case_noncollapse Γ iid np discr alts hwc]
    refine .iota (k := k) (cargs := LBOptimizeArgs Γ cargs)
      (names := names) (body := LBOptimize Γ body) ?_ ?_ ?_
    · simpa using ihd
    · rw [LBOptimizeAlts_eq_map, List.getElem?_map, hsel]; rfl
    · rw [LBOptimizeArgs_eq_map, ← LBOptimize_substList Γ cargs body]
      exact ihbody
  | @iota_box iid np discr names body r hp _ _ ihd ihbody =>
    rw [LBOptimize_case_collapse Γ iid np discr names body hp]
    rw [← LBOptimize_substList_box Γ names.length body]
    exact ihbody

/-! ## Vacuity guard for `LBOptimize_correct`.

`LBOptimize_correct` is hypothesis-bearing (`EvalProp Γ t v → …`).  We rule out
vacuous truth three ways:

* `LBOptimize_correct_not_refutable` — the statement is *not* `EvalProp → False`
  (there exist `Γ, t, v` with `EvalProp Γ t v`), so the hypothesis is
  inhabitable;
* `LBOptimize_correct_hyps_satisfiable` — a concrete positive witness of the
  premise;
* `LBOptimize_correct_fires` — applies the theorem to a concrete
  *collapsing* prop-case, obtaining genuine `Eval` content (not `True`).

The witness environment `vacΓ` declares one propositional, single-constructor
inductive `P` (so `isPropositionalInductive vacΓ vacIid = true`). The witness
term is the single-branch case `case (vacIid, 0) box [([anon], bvar 0)]`, which:
* collapses under `LBOptimize` (prop + single branch) to `box`, and
* evaluates under `EvalProp` via `iota_box` (discriminant `box`, sole branch's
  field replaced by `box`, `substList [box] (bvar 0) = box`). -/

/-- Witness kername for the propositional inductive block. -/
def vacKn : Kername := { mp := .MPfile [], id := "P" }

/-- Witness inductive id (block `vacKn`, body 0). -/
def vacIid : InductiveId := { mutualBlockName := vacKn, idx := 0 }

/-- A propositional single-constructor inductive body (one field). -/
def vacOIB : OneInductiveBody :=
  { name := "P", propositional := true, kelim := .IntoAny,
    ctors := [{ name := "mkP", nargs := 1 }], projs := [] }

/-- Witness environment: just the propositional inductive `P`. -/
def vacΓ : GlobalDeclarations :=
  [(vacKn, .inductiveDecl { finite := .finite, npars := 0, bodies := [vacOIB] })]

/-- The witness collapsing prop-case term. -/
def vacTerm : LBTerm :=
  .case (vacIid, 0) .box [([.anon], .bvar 0)]

theorem vac_isProp : isPropositionalInductive vacΓ vacIid = true := by
  rfl

/-- Sanity: the witness term actually collapses to `box` under `LBOptimize`. -/
theorem vac_optimize_collapses : LBOptimize vacΓ vacTerm = .box := by
  rfl

/-- (ii) The premise of `LBOptimize_correct` is satisfiable: `EvalProp` holds on
    the witness, with result `box`. -/
theorem LBOptimize_correct_hyps_satisfiable :
    EvalProp vacΓ vacTerm .box := by
  refine EvalProp.iota_box (names := [.anon]) (body := .bvar 0) vac_isProp .box ?_
  -- substList [box] (bvar 0) = box, and EvalProp box box
  show EvalProp vacΓ (LBTerm.substList (List.replicate 1 .box) (.bvar 0)) .box
  rw [show LBTerm.substList (List.replicate 1 .box) (.bvar 0) = .box from rfl]
  exact .box

/-- (i) Non-refutability: the hypothesis can hold, so the implication is not
    vacuously true via an empty antecedent. -/
theorem LBOptimize_correct_not_refutable :
    ∃ Γ t v, EvalProp Γ t v :=
  ⟨vacΓ, vacTerm, .box, LBOptimize_correct_hyps_satisfiable⟩

/-- (iii) Firing the theorem on the concrete collapsing prop-case yields genuine
    `Eval` content: the optimized term `box` evaluates to `box` in the optimized
    environment.  This is real (non-`True`) output of `LBOptimize_correct`. -/
theorem LBOptimize_correct_fires :
    Eval (LBOptimize_env vacΓ) .box .box := by
  have h : Eval (LBOptimize_env vacΓ) (LBOptimize vacΓ vacTerm) (LBOptimize vacΓ .box) :=
    LBOptimize_correct LBOptimize_correct_hyps_satisfiable
  -- both sides optimize to `box`
  simpa [vac_optimize_collapses] using h

end LeanToLambdaBox
