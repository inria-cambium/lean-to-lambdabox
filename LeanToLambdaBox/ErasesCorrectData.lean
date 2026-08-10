import LeanToLambdaBox.Erases
import LeanToLambdaBox.Eval
import LeanToLambdaBox.Semantics.Metatheory
import LeanToLambdaBox.SubjectReduction
import LeanToLambdaBox.SubjectReductionFull
import LeanToLambdaBox.SourceEvalData
import LeanToLambdaBox.ErasesCorrect
import LeanToLambdaBox.EraseCore

/-!
# Erasure correctness for the data fragment (steps A5–A7)

Forward simulation `erases_correct_data` at MetaRocq's non-block `appliedFlags`
(`with_constructor_as_block = false`), for the source relation `SEvalData`
(β + ζ + δ + saturated constructor values). This is the data-fragment counterpart of
`erases_correct` (β + δ, targeting the block `Eval`).

## Why the erasure must be applied (non-block) form: `NoBlock`

`appliedFlags` is MetaRocq's *non-block* mode: a saturated constructor **value** is a
spine `mkApps (.construct iid c []) vs` built by `construct_atom`/`construct_app`
(one argument at a time). The `WcbvEval` `construct` rule (args carried inside the
node, `.construct iid c args`) fires **only** at `with_constructor_as_block = true`, so
a nonempty block constructor node is genuinely **stuck** at `appliedFlags`.

The erasure relation `Erases`, however, keeps *both* forms: the abstract block rule
`Erases.ctor` (args inside — MetaRocq's internal representation) *and* the applied
`Erases.ctor_head` (bare `.construct iid c []` wrapped by `Erases.app`, what the
shipping `visitConstApp` emits). A forward simulation at `appliedFlags` can therefore
only hold for the **applied** erasures. We capture this with the structural predicate
`NoBlock` (no nonempty `.construct` node) as an explicit premise; it is *true for every
shipping / `eraseCore` erasure* (both produce applied form), and the theorem produces
`NoBlock` of the value too, so the premise threads through the induction. The block
`ctor` derivation (`blockcut`, `A6`) is discharged against `NoBlock`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean


/-! ## `NoBlock`: applied-form erasures only

`NoBlock t` holds when `t` contains no *nonempty* block-constructor node
`.construct iid c (_ :: _)`. The nullary node `.construct iid c []` (the base of a
non-block spine, MetaRocq's `atom (tConstruct ind c [])`) is allowed. `case`/`proj`/
`fix` are treated opaquely (`True`) — the data fragment of `erases_correct_data` never
produces them (they belong to the `casesOn`/recursor work, C1–C3/P3). -/
def NoBlock : LBTerm → Prop
  | .lambda _ b => NoBlock b
  | .letIn _ v b => NoBlock v ∧ NoBlock b
  | .app f a => NoBlock f ∧ NoBlock a
  | .construct _ _ [] => True
  | .construct _ _ (_ :: _) => False
  | _ => True

@[simp] theorem NoBlock_box : NoBlock .box := trivial
@[simp] theorem NoBlock_bvar (i : Nat) : NoBlock (.bvar i) := trivial
@[simp] theorem NoBlock_fvar (x : FVarId) : NoBlock (.fvar x) := trivial
@[simp] theorem NoBlock_const (kn : Kername) : NoBlock (.const kn) := trivial
@[simp] theorem NoBlock_construct_nil (iid : InductiveId) (c : Nat) :
    NoBlock (.construct iid c []) := trivial
@[simp] theorem NoBlock_lambda (n : BinderName) (b : LBTerm) :
    NoBlock (.lambda n b) ↔ NoBlock b := Iff.rfl
@[simp] theorem NoBlock_letIn (n : BinderName) (v b : LBTerm) :
    NoBlock (.letIn n v b) ↔ NoBlock v ∧ NoBlock b := Iff.rfl
@[simp] theorem NoBlock_app (f a : LBTerm) :
    NoBlock (.app f a) ↔ NoBlock f ∧ NoBlock a := Iff.rfl

/-- `NoBlock` is preserved by de Bruijn shifting. -/
theorem noBlock_shift {s : LBTerm} (hs : NoBlock s) (d c : Nat) :
    NoBlock (LBTerm.shift d c s) := by
  induction s using LBTerm.recData generalizing c with
  | hbvar i => simp only [LBTerm.shift]; split <;> trivial
  | hlam n b ih => exact ih hs (c + 1)
  | hletIn n v b ihv ihb => exact ⟨ihv hs.1 c, ihb hs.2 (c + 1)⟩
  | happ f a ihf iha => exact ⟨ihf hs.1 c, iha hs.2 c⟩
  | hconstruct iid k args _ =>
      cases args with
      | nil => simp only [LBTerm.shift, LBTerm.shiftArgs]; trivial
      | cons a as => exact absurd hs (by simp [NoBlock])
  | _ => trivial

/-- `NoBlock` is preserved by substitution (the substitutee `s` must be `NoBlock`
too, since it lands at bvar positions). -/
theorem noBlock_subst {t : LBTerm} (ht : NoBlock t) {s : LBTerm} (hs : NoBlock s)
    (d : Nat) : NoBlock (LBTerm.subst s d t) := by
  induction t using LBTerm.recData generalizing d with
  | hbvar i =>
      simp only [LBTerm.subst]
      split
      · trivial
      · split
        · exact noBlock_shift hs d 0
        · trivial
  | hlam n b ih => exact ih ht (d + 1)
  | hletIn n v b ihv ihb => exact ⟨ihv ht.1 d, ihb ht.2 (d + 1)⟩
  | happ f a ihf iha => exact ⟨ihf ht.1 d, iha ht.2 d⟩
  | hconstruct iid k args _ =>
      cases args with
      | nil => simp only [LBTerm.subst, LBTerm.substArgs]; trivial
      | cons a as => exact absurd ht (by simp [NoBlock])
  | _ => trivial

theorem noBlock_subst1 {t s : LBTerm} (ht : NoBlock t) (hs : NoBlock s) :
    NoBlock (LBTerm.subst1 s t) := noBlock_subst ht hs 0

/-- A `NoBlock`-headed application spine with `NoBlock` arguments is `NoBlock`. -/
theorem noBlock_mkApps {hd : LBTerm} (hhd : NoBlock hd) {args : List LBTerm}
    (h : ∀ a ∈ args, NoBlock a) : NoBlock (LBTerm.mkApps hd args) := by
  induction args generalizing hd with
  | nil => exact hhd
  | cons a as ih =>
      rw [LBTerm.mkApps]
      exact ih ⟨hhd, h a (List.mem_cons_self ..)⟩ (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- The head of a `NoBlock` application spine is `NoBlock`. -/
theorem noBlock_mkApps_head {hd : LBTerm} {args : List LBTerm}
    (h : NoBlock (LBTerm.mkApps hd args)) : NoBlock hd := by
  induction args generalizing hd with
  | nil => exact h
  | cons a as ih => rw [LBTerm.mkApps] at h; exact (ih h).1

/-- Each argument of a `NoBlock` application spine is `NoBlock`. -/
theorem noBlock_mkApps_inv {hd : LBTerm} {args : List LBTerm}
    (h : NoBlock (LBTerm.mkApps hd args)) : ∀ a ∈ args, NoBlock a := by
  induction args generalizing hd with
  | nil => intro a ha; exact absurd ha (by simp)
  | cons a as ih =>
      rw [LBTerm.mkApps] at h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (noBlock_mkApps_head h).2
      · exact ih h x hx

/-- A box-headed application spine is `NoBlock`. -/
theorem noBlock_mkApps_box {args : List LBTerm} (h : ∀ a ∈ args, NoBlock a) :
    NoBlock (LBTerm.mkApps .box args) := noBlock_mkApps NoBlock_box h

/-- A nullary-constructor-headed application spine is `NoBlock`. -/
theorem noBlock_mkApps_construct {iid : InductiveId} {c : Nat} {args : List LBTerm}
    (h : ∀ a ∈ args, NoBlock a) :
    NoBlock (LBTerm.mkApps (.construct iid c []) args) :=
  noBlock_mkApps (NoBlock_construct_nil iid c) h

/-! ## A5: target spine accumulation at `appliedFlags`

Accumulating a list of value-evaluating arguments onto a partial (under-arity)
non-block constructor spine `mkApps (.construct iid c []) pre` yields the extended
spine, provided the total stays within the constructor arity. Snoc/front induction,
each step firing `WcbvEval.construct_app`. sorryAx-free. -/

/-- **A5.** If `f` evaluates to a partial constructor spine `mkApps (.construct iid c
[]) pre` (under the arity), and `args` evaluate pointwise to `vs`, then applying `f`
to `args` (left fold) evaluates to `mkApps (.construct iid c []) (pre ++ vs)` — as
long as `pre.length + args.length ≤ ar`. -/
theorem construct_app_spine {Γ : GlobalDeclarations} {iid : InductiveId} {c ar : Nat}
    (harity : constructorArity Γ iid c = some ar) :
    ∀ (args vs : List LBTerm) (f : LBTerm) (pre : List LBTerm),
      WcbvEval Γ appliedFlags f (LBTerm.mkApps (.construct iid c []) pre) →
      pre.length + args.length ≤ ar →
      (hl : args.length = vs.length) →
      (∀ i (h : i < args.length), WcbvEval Γ appliedFlags args[i] (vs[i]'(hl ▸ h))) →
      WcbvEval Γ appliedFlags (args.foldl LBTerm.app f)
        (LBTerm.mkApps (.construct iid c []) (pre ++ vs)) := by
  intro args
  induction args with
  | nil =>
      intro vs f pre hf _ hl _
      have hvs : vs = [] := List.eq_nil_of_length_eq_zero hl.symm
      subst hvs
      simpa using hf
  | cons a as ih =>
      intro vs f pre hf hle hl hargs
      cases vs with
      | nil => simp at hl
      | cons v vsr =>
          have hav : WcbvEval Γ appliedFlags a v := by
            have := hargs 0 (by simp); simpa using this
          have hbound : pre.length + as.length + 1 ≤ ar := by
            simp only [List.length_cons] at hle; omega
          have hlt : pre.length < ar := by omega
          have step : WcbvEval Γ appliedFlags (LBTerm.app f a)
              (LBTerm.mkApps (.construct iid c []) (pre ++ [v])) := by
            rw [LBTerm.mkApps_concat]
            exact .construct_app rfl hf harity hlt hav
          have hle' : (pre ++ [v]).length + as.length ≤ ar := by
            simp only [List.length_append, List.length_cons, List.length_nil]; omega
          have hl' : as.length = vsr.length := by simpa using hl
          have hargs' : ∀ i (h : i < as.length),
              WcbvEval Γ appliedFlags as[i] (vsr[i]'(hl' ▸ h)) := by
            intro i h
            have := hargs (i + 1) (by simp only [List.length_cons]; omega)
            simpa using this
          have hmain := ih vsr (LBTerm.app f a) (pre ++ [v]) step hle' hl' hargs'
          rw [List.foldl_cons]
          rw [List.append_assoc, List.singleton_append] at hmain
          exact hmain

/-- `mkApps` is a left fold of application (`mkApps f l = l.foldl app f`). -/
theorem mkApps_eq_foldl (f : LBTerm) (l : List LBTerm) :
    LBTerm.mkApps f l = l.foldl LBTerm.app f := by
  induction l generalizing f with
  | nil => rfl
  | cons a as ih => rw [LBTerm.mkApps, List.foldl_cons, ih]

/-- A box-headed application spine evaluates to `box`, provided each argument
    evaluates to some value (MetaRocq `eval_box` fold). -/
theorem mkApps_headBox_eval {Γ : GlobalDeclarations} {hd : LBTerm}
    (hhd : WcbvEval Γ appliedFlags hd .box) {args : List LBTerm}
    (h : ∀ a ∈ args, ∃ v, WcbvEval Γ appliedFlags a v) :
    WcbvEval Γ appliedFlags (LBTerm.mkApps hd args) .box := by
  induction args generalizing hd with
  | nil => exact hhd
  | cons a as ih =>
      rw [LBTerm.mkApps]
      obtain ⟨v, hv⟩ := h a (List.mem_cons_self ..)
      exact ih (WcbvEval.app_box hhd hv) (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-! ## Erasing an application spine

`Erases` of `vs.foldl Expr.app head` given the head's erasure and each argument's,
in the applied (`mkApps`) form. Front induction with a generalized head. -/

/-- If `head` erases to `head'` and each `vs[i]` erases to `vs'[i]`, then the source
spine `vs.foldl Expr.app head` erases to `mkApps head' vs'`. -/
theorem erases_app_spine {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx}
    {head : Expr} {head' : LBTerm} (hhead : Erases env Us Γ Δ head head') :
    ∀ (vs : List Expr) (vs' : List LBTerm) (hl : vs.length = vs'.length),
      (∀ i (h : i < vs.length), Erases env Us Γ Δ vs[i] (vs'[i]'(hl ▸ h))) →
      Erases env Us Γ Δ (vs.foldl Expr.app head) (LBTerm.mkApps head' vs') := by
  intro vs
  induction vs generalizing head head' with
  | nil =>
      intro vs' hl _
      have : vs' = [] := List.eq_nil_of_length_eq_zero hl.symm
      subst this
      simpa using hhead
  | cons a as ih =>
      intro vs' hl hargs
      cases vs' with
      | nil => simp at hl
      | cons a' as' =>
          have ha : Erases env Us Γ Δ a a' := by
            have := hargs 0 (by simp); simpa using this
          have hl' : as.length = as'.length := by simpa using hl
          have hargs' : ∀ i (h : i < as.length), Erases env Us Γ Δ as[i] (as'[i]'(hl' ▸ h)) := by
            intro i h
            have := hargs (i + 1) (by simp only [List.length_cons]; omega)
            simpa using this
          have hstep := ih (.app hhead ha) as' hl' hargs'
          rw [List.foldl_cons]
          rw [LBTerm.mkApps]
          exact hstep

/-- **Pointwise choice over an index range.** Collects per-index existentials into a
concrete list (used to assemble the value list from the per-argument IHs). -/
theorem choose_list {α : Type} {P : Nat → α → Prop} :
    ∀ (n : Nat), (∀ i, i < n → ∃ a, P i a) →
      ∃ (l : List α), l.length = n ∧ ∀ i (hi : i < l.length), P i (l[i]'hi)
  | 0, _ => ⟨[], rfl, fun i hi => absurd hi (by simp)⟩
  | n + 1, h => by
      obtain ⟨a0, ha0⟩ := h 0 (by omega)
      obtain ⟨l, hlen, hl⟩ := choose_list (P := fun i => P (i + 1)) n (fun i hi => h (i + 1) (by omega))
      refine ⟨a0 :: l, by simp [hlen], fun i hi => ?_⟩
      cases i with
      | zero => simpa using ha0
      | succ j =>
          have hj : j < l.length := by simpa using hi
          simpa using hl j hj

/-! ## A6: classifying the erasure of a constructor application spine

`Erases.ctor_spine_inv` inverts `Erases (args.foldl Expr.app (.const cn us)) t` for a
registered constructor head. The four MetaRocq-relevant shapes ("cuts"):

* **root-box / boxcut** — the whole spine (or a proper prefix) is irrelevant and
  boxed; `t = mkApps .box args'` (a box-headed spine over a suffix of `args`) and the
  whole spine is `Erasable`. The `Erasable` witness of a boxed prefix is propagated
  outward with `Erasable.app`.
* **headcut** — the applied form the shipping emits: the head erases via `ctor_head`
  to `.construct iid cidx []`, wrapped by `Erases.app`; `t = mkApps (.construct iid
  cidx []) args'` over all of `args`.
* **blockcut** (and any block-node junk) — the abstract `Erases.ctor` block rule (or
  a block node under further application); returned as `¬ NoBlock t`, so the caller
  discharges it against its `NoBlock` premise.

The `casesOns`-disjointness premise `hcas` rules out the `cases` rule firing on a
constructor head (their heads would have to coincide). -/

/-- Head of an `Expr` application spine peels through the `foldl`. -/
theorem expr_getAppFn_foldl (f : Expr) (args : List Expr) :
    (args.foldl Expr.app f).getAppFn = f.getAppFn := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih]; rfl

/-- **t-preserving inversion of `Erases` on an application node.** Unlike
`Erases.app_inv`, the block-`ctor` and `cases` disjuncts retain the target `t`
(needed by A6 to detect the block form). -/
theorem Erases.app_inv_t {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx}
    {f a : Expr} {t : LBTerm} (h : Erases env Us Γ Δ (.app f a) t) :
    (∃ ve, TrExprS env Us Δ (.app f a) ve ∧
        Erasable env Us.length Δ.toCtx ve ∧ t = .box) ∨
    (∃ f' a', Erases env Us Γ Δ f f' ∧ Erases env Us Γ Δ a a' ∧ t = .app f' a') ∨
    (∃ (cn : Name) (us : List Level) (args2 : List Expr) (iid : InductiveId) (cidx : Nat)
        (args' : List LBTerm),
        Expr.app f a = args2.foldl Expr.app (.const cn us) ∧
        Γ.ctors cn = some (iid, cidx) ∧ args2.length = args'.length ∧
        t = .construct iid cidx args') ∨
    (∃ (con : Name) (us : List Level) (pre : List Expr) (discr : Expr) (minors : List Expr)
        (iid : InductiveId) (np : Nat) (discr' : LBTerm)
        (alts' : List (List BinderName × LBTerm)),
        Expr.app f a = (discr :: minors).foldl Expr.app (pre.foldl Expr.app (.const con us)) ∧
        Γ.casesOns con = some (iid, np) ∧ t = .case (iid, np) discr' alts') := by
  generalize he : (Expr.app f a) = e₀ at h
  induction h with
  | box htr' her' => subst he; exact .inl ⟨_, htr', her', rfl⟩
  | app hf ha => cases he; exact .inr (.inl ⟨_, _, hf, ha, rfl⟩)
  | @ctor _ cn us iid cidx args args' hc hlen _ _ =>
      exact .inr (.inr (.inl ⟨cn, us, args, iid, cidx, args', rfl, hc, hlen, rfl⟩))
  | @cases _ con us iid np pre discr discr' minors alts' _ hcase _ _ _ _ _ _ =>
      exact .inr (.inr (.inr ⟨con, us, pre, discr, minors, iid, np, discr', alts',
        rfl, hcase, rfl⟩))
  | _ => exact absurd he (by simp)

/-- **`.const`-source inversion keeping the `ctors = none` witness** (which
`const_inv` discards) — needed to exclude the plain-`const` rule on a registered
constructor head. -/
theorem Erases.const_inv_full {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx}
    {n : Name} {us : List Level} {t : LBTerm} (h : Erases env Us Γ Δ (.const n us) t) :
    (∃ ve, TrExprS env Us Δ (.const n us) ve ∧
        Erasable env Us.length Δ.toCtx ve ∧ t = .box) ∨
    (∃ kn, Γ.constants n = kn ∧ Γ.ctors n = none ∧ t = .const kn) ∨
    (∃ (iid : InductiveId) (cidx : Nat), Γ.ctors n = some (iid, cidx) ∧
        t = .construct iid cidx []) := by
  generalize he : (Expr.const n us) = e₀ at h
  induction h with
  | box htr' her' => subst he; exact .inl ⟨_, htr', her', rfl⟩
  | const m ms kn hkn hctor _ => cases he; exact .inr (.inl ⟨_, hkn, hctor, rfl⟩)
  | ctor_head cn cus iid cidx hc => cases he; exact .inr (.inr ⟨iid, cidx, hc, rfl⟩)
  | @ctor _ cn cus iid cidx args args' hc hlen _ _ =>
      rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
      · simp only [List.foldl] at he
        cases he
        have : args' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
        subst this
        exact .inr (.inr ⟨iid, cidx, hc, rfl⟩)
      · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil] at he
        exact absurd he (by simp)
  | @cases _ con cus _ numParams pre discr _ minors _ _ _ _ _ _ _ =>
      simp only [List.foldl_cons] at he
      rcases foldl_app_eq_or_isApp ((pre.foldl Expr.app (.const con cus)).app discr)
        minors with hh | hh
      · rw [← he] at hh; simp at hh
      · rw [← he] at hh; simp [Expr.isApp] at hh
  | _ => exact absurd he (by simp)

/-- **A6 — classification of a constructor-spine erasure.** Under a registered head
`cn` (with `casesOns`-disjointness), the erasure of `args.foldl Expr.app (.const cn
us)` is one of: box-headed (`t = mkApps .box args'`, whole spine `Erasable`, each
`args'` element erasing some source arg — root-box/boxcut); applied ctor
(`t = mkApps (.construct iid cidx []) args'` over all args — headcut); or a block-form
node (`¬ NoBlock t` — blockcut). -/
theorem Erases.ctor_spine_inv {env : VEnv} (henv : env.WF) {Us : List Name}
    {Γ : ErasureCtx} {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length Δ)
    {cn : Name} {us : List Level} {iid : InductiveId} {cidx : Nat}
    (hc : Γ.ctors cn = some (iid, cidx)) (hcas : Γ.casesOns cn = none) :
    ∀ (m : Nat) (args : List Expr), args.length = m → ∀ {ve : VExpr} {t : LBTerm},
      TrExprS env Us Δ (args.foldl Expr.app (.const cn us)) ve →
      Erases env Us Γ Δ (args.foldl Expr.app (.const cn us)) t →
      (Erasable env Us.length Δ.toCtx ve ∧
        ∃ (args' : List LBTerm), t = LBTerm.mkApps .box args' ∧
          ∀ a' ∈ args', ∃ sa ∈ args, Erases env Us Γ Δ sa a') ∨
      (∃ (args' : List LBTerm) (hlen : args.length = args'.length),
        t = LBTerm.mkApps (.construct iid cidx []) args' ∧
        ∀ i (h : i < args'.length), Erases env Us Γ Δ (args[i]'(hlen ▸ h)) (args'[i]'h)) ∨
      ¬ NoBlock t := by
  have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro args hm ve t htr her
    rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
    · -- base: args = []
      simp only [List.foldl] at htr her
      rcases her.const_inv_full with ⟨ve', htr', her', rfl⟩ | ⟨kn, _, hctor, rfl⟩
        | ⟨iid2, cidx2, hc2, rfl⟩
      · refine .inl ⟨?_, [], rfl, by simp⟩
        exact her'.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htr' htr)
      · rw [hc] at hctor; exact absurd hctor (by simp)
      · rw [hc] at hc2; injection hc2 with hpair; injection hpair with h1 h2; subst h1; subst h2
        exact .inr (.inl ⟨[], rfl, by simp [LBTerm.mkApps], fun i h => absurd h (by simp)⟩)
    · -- step: args = init ++ [last]
      simp only [List.concat_eq_append] at hm htr her ⊢
      have hspine : (init ++ [last]).foldl Expr.app (.const cn us)
          = Expr.app (init.foldl Expr.app (.const cn us)) last := by
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hspine] at htr her
      cases htr with
      | @app fve A B lastve _ _ _ hTf hTa htrf htrlast =>
        rcases her.app_inv_t with
          ⟨ve', htr'app, her'box, rfl⟩ |
          ⟨f', last', hf', hlast', rfl⟩ |
          ⟨cn2, us2, args2, iid2, cidx2, args'', hsrc, hc2, hlen2, rfl⟩ |
          ⟨con, us2, pre, discr, minors, iid2, np, discr', alts', hsrc, hcase2, rfl⟩
        · -- box on the whole current spine
          refine .inl ⟨?_, [], rfl, by simp⟩
          exact her'box.defeq henv hΓ
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ)
              htr'app (.app hTf hTa htrf htrlast))
        · -- structural application: recurse on the init spine
          have hlt : init.length < m := by
            have : (init ++ [last]).length = m := hm
            simp only [List.length_append, List.length_singleton] at this; omega
          rcases ih init.length hlt init rfl htrf hf' with
            ⟨herasePre, args'', heqt, hmem⟩ | ⟨args'', hlen'', heqt, hcorr⟩ | hnb
          · -- box-case for init → box-case for the whole spine (Erasable.app)
            refine .inl ⟨herasePre.app henv hΓ hTf hTa, args'' ++ [last'], ?_, ?_⟩
            · rw [heqt, LBTerm.mkApps_concat]
            · intro a' ha'
              rcases List.mem_append.mp ha' with h | h
              · obtain ⟨sa, hsa, hera⟩ := hmem a' h
                exact ⟨sa, List.mem_append_left _ hsa, hera⟩
              · rw [List.mem_singleton] at h; subst h
                exact ⟨last, List.mem_append_right _ (List.mem_singleton_self _), hlast'⟩
          · -- headcut for init → headcut for the whole spine
            refine .inr (.inl ⟨args'' ++ [last'], ?_, ?_, ?_⟩)
            · simp only [List.length_append, List.length_singleton]; omega
            · rw [heqt, LBTerm.mkApps_concat]
            · intro i h
              simp only [List.length_append, List.length_singleton] at h
              by_cases hi : i < init.length
              · rw [List.getElem_append_left (by simpa using hi),
                  List.getElem_append_left (by omega)]
                exact hcorr i (by omega)
              · have hieq : i = init.length := by omega
                subst hieq
                rw [List.getElem_append_right (by omega),
                  List.getElem_append_right (by simp [hlen''])]
                simp only [hlen'', Nat.sub_self, List.getElem_cons_zero]
                simpa using hlast'
          · -- init erasure is block → so is the whole (t = .app f' last')
            exact .inr (.inr (fun hnbt => hnb hnbt.1))
        · -- block ctor rule: t = .construct (nonempty) → ¬ NoBlock
          refine .inr (.inr ?_)
          have hargs2_ne : args2 ≠ [] := by
            intro h; subst h; simp only [List.foldl_nil] at hsrc
            rw [← hspine] at hsrc; exact absurd hsrc (by simp)
          have : args''.length ≠ 0 := by
            rw [← hlen2]; exact fun h => hargs2_ne (List.eq_nil_of_length_eq_zero h)
          cases args'' with
          | nil => exact absurd rfl this
          | cons x xs => simp [NoBlock]
        · -- cases rule on a ctor head: contradicts casesOns-disjointness
          exfalso
          have hfn : (Expr.app (init.foldl Expr.app (.const cn us)) last).getAppFn
              = Expr.const cn us := by
            rw [← hspine]; rw [expr_getAppFn_foldl]; rfl
          have hfn2 : (Expr.app (init.foldl Expr.app (.const cn us)) last).getAppFn
              = Expr.const con us2 := by
            rw [hsrc]; rw [expr_getAppFn_foldl, expr_getAppFn_foldl]; rfl
          rw [hfn] at hfn2; injection hfn2 with hcncon
          rw [← hcncon, hcas] at hcase2; exact absurd hcase2 (by simp)

/-! ## A7: forward simulation for the data fragment (`erases_correct_data`)

Env consistency hypotheses beyond `erases_correct`'s:

* `ErasesEnvCtor` — the target env's constructor arity matches `Γ.ctorArities` (so
  `construct_atom`/`construct_app` fire with the right bound), and
* `ErasesEnvDeltaData` — the target-side δ link (as `ErasesEnvDelta`) that also
  certifies the unfolded body erases to **applied (`NoBlock`) form**.
-/

/-- **Target-side constructor arity agreement.** `Γ.ctorArities` matches the target
env's `constructorArity`. -/
def ErasesEnvCtor (Γ : ErasureCtx) (E : GlobalDeclarations) : Prop :=
  ∀ {cn : Name} {iid : InductiveId} {cidx ar : Nat},
    Γ.ctors cn = some (iid, cidx) → Γ.ctorArities cn = some ar →
    constructorArity E iid cidx = some ar

/-- **Target-side δ consistency for the data fragment.** As `ErasesEnvDelta`, plus the
unfolded constant body erases to **applied (`NoBlock`) form** (so the δ IH stays in
the appliedFlags-simulable fragment). -/
def ErasesEnvDeltaData (env : VEnv) (Us : List Name) (Γ : ErasureCtx)
    (Esrc : SEnv) (E : GlobalDeclarations) : Prop :=
  ∀ {Δ : VLCtx} {n : Name} {body : Expr},
    Esrc n = some body →
    Γ.ctors n = none ∧ Γ.casesOns n = none ∧
    ∃ body', LBTerm.envLookup E (Γ.constants n) = some (.constantDecl ⟨some body'⟩) ∧
      Erases env Us Γ Δ body body' ∧ NoBlock body'

/-- The **β + δ + saturated-constructor** fragment of `SEvalData` (dropping `zeta`).
This is the fragment for which `erases_correct_data` is proved fully sorry-free at
`appliedFlags`. The ζ case is handled separately in `erases_correct_data_zeta` (over
the full `SEvalData`, β+ζ+δ+ctor): the target ζ substitutes the **evaluated** value
`vtv` (`v' ⇓ vtv`), but `erases_subst_let` bakes the `vlet`'s *stored* translation into
its substitutee, so the ζ reduct `b[vv]` needs a **depth-generalized `vlet`-value
context-defeq transport for `Erases`** — this is `Erases.defeqDFC` (a `VLCtx.IsDefEq`
transport, the `Erases` analogue of `TrExprS.defeqDFC`), which swaps the `vlet`'s stored
value for the translation of the evaluated value before `erases_subst_let` fires. -/
inductive SEvalDataC (Γ : ErasureCtx) (E : SEnv) : Expr → Expr → Prop
  | lam (n : Name) (ty b : Expr) (bi : BinderInfo) :
      SEvalDataC Γ E (.lam n ty b bi) (.lam n ty b bi)
  | beta {f a : Expr} {n : Name} {ty b : Expr} {bi : BinderInfo} {av r : Expr} :
      SEvalDataC Γ E f (.lam n ty b bi) → SEvalDataC Γ E a av →
      SEvalDataC Γ E (b.instantiate1' av 0) r →
      SEvalDataC Γ E (.app f a) r
  | delta {n : Name} {us : List Level} {body r : Expr} :
      E n = some body → SEvalDataC Γ E body r → SEvalDataC Γ E (.const n us) r
  | ctor_val {cn : Name} {us : List Level} {iid : InductiveId} {cidx ar : Nat}
      {args vs : List Expr}
      (hc : Γ.ctors cn = some (iid, cidx))
      (har : Γ.ctorArities cn = some ar)
      (hsat : args.length ≤ ar)
      (hl : args.length = vs.length)
      (hargs : ∀ i (h : i < args.length), SEvalDataC Γ E args[i] (vs[i]'(hl ▸ h))) :
      SEvalDataC Γ E (args.foldl Expr.app (.const cn us))
        (vs.foldl Expr.app (.const cn us))

/-- Embedding into the full (β+ζ+δ+ctor) `SEvalData`. -/
theorem SEvalDataC.toSEvalData {Γ : ErasureCtx} {E : SEnv} {e v : Expr}
    (h : SEvalDataC Γ E e v) : SEvalData Γ E e v := by
  induction h with
  | lam n ty b bi => exact .lam n ty b bi
  | beta _ _ _ ihf iha ihb => exact .beta ihf iha ihb
  | delta hu _ ih => exact .delta hu ih
  | ctor_val hc har hsat hl _ ihargs => exact .ctor_val hc har hsat hl (fun i h => ihargs i h)

/-- **Erasure correctness — forward simulation, β + δ + saturated constructors, at
MetaRocq's non-block `appliedFlags`.**

If the source `e` translates to `ve`, erases to an **applied-form** (`NoBlock`) target
`t`, and evaluates to `v` under `SEvalDataC` (β/δ + saturated constructor values),
then `t` evaluates (`WcbvEval E appliedFlags`) to some `t'` that erases `v`, with `t'`
applied form and `v` translating to some `vve`.

Threads `SEnvConsistent` (source↔`VEnv` δ link for the `box` subject-reduction cases),
`ErasesEnvDeltaData` (target δ link + applied-form bodies), `ErasesEnvCtor` (arity
agreement), and `hcc` (`ctors`/`casesOns` disjointness). -/
theorem erases_correct_data {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {Γ : ErasureCtx} {Esrc : SEnv} {E : GlobalDeclarations}
    (hcon : SEnvConsistent env Us Esrc)
    (hdelta : ErasesEnvDeltaData env Us Γ Esrc E)
    (hctorenv : ErasesEnvCtor Γ E)
    (hcc : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
             Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none)
    (hnfenv : NoFixEnv E)
    {e v : Expr} (hev : SEvalDataC Γ Esrc e v) :
    ∀ {ve : VExpr} {t : LBTerm},
      TrExprS env Us Δ e ve → Erases env Us Γ Δ e t → NoBlock t → NoFix t →
      ∃ t' vve, WcbvEval E appliedFlags t t' ∧ TrExprS env Us Δ v vve ∧
        Erases env Us Γ Δ v t' ∧ NoBlock t' ∧ NoFix t' := by
  have hnf : ∀ {n : Name} {body : Expr}, Esrc n = some body →
      Γ.ctors n = none ∧ Γ.casesOns n = none :=
    fun h => ⟨(hdelta (Δ := Δ) h).1, (hdelta (Δ := Δ) h).2.1⟩
  induction hev with
  | lam n ty b bi =>
      intro ve t htr her hnb hnfx
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      rcases Erases.lam_inv her with ⟨veb, htrb, herbox, rfl⟩ | ⟨_, _, hty, hb, rfl⟩
        | ⟨defs, idx, rfl, _⟩
      · exact ⟨.box, ve, .box, htr, .box htr
          (herbox.defeq henv hΓ
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)), trivial, trivial⟩
      · exact ⟨_, ve, .lam _ _, htr, .lam hty hb, hnb, hnfx⟩
      · exact hnfx.elim
  | @beta f a n ty b bi av r hf ha hbody ihf iha ihbody =>
      intro ve t htr her hnb hnfx
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      rcases Erases.app_inv her with
        ⟨veb, htrb, herbox, rfl⟩ | ⟨f't, a't, hf', ha', rfl⟩ | ⟨cn, us, args, hspine, hmem⟩
      · obtain ⟨vve, htrr, hdef⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.beta hf.toSEvalData.toβζδ ha.toSEvalData.toβζδ hbody.toSEvalData.toβζδ)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hdef), trivial, trivial⟩
      · cases htr with
        | @app f' A B a'' _Δ _f _a hTf hTa htrf htra =>
          obtain ⟨ftv, fvv, hEf, htrlam, herlam, hnbftv, hnfftv⟩ := ihf htrf hf' hnb.1 hnfx.1
          rcases Erases.lam_inv herlam with ⟨velam, htrvelam, herlamE, rfl⟩
            | ⟨tyE, b', htrtyE, hb', rfl⟩ | ⟨defs, idx, rfl, _⟩
          · obtain ⟨vve, htrr, hdef⟩ :=
              SEvalβζδ_defeq henv hΔ hcon (.app hTf hTa htrf htra)
                (.beta hf.toSEvalData.toβζδ ha.toSEvalData.toβζδ hbody.toSEvalData.toβζδ)
            obtain ⟨fvv0, htrlam0, hfdef⟩ := SEvalβζδ_defeq henv hΔ hcon htrf hf.toSEvalData.toβζδ
            have hferase : Erasable env Us.length Δ.toCtx f' :=
              (herlamE.defeq henv hΓ
                (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrvelam htrlam0)).defeq
                henv hΓ (VEnv.IsDefEqU.symm hfdef)
            have herapp : Erasable env Us.length Δ.toCtx (.app f' a'') :=
              hferase.app henv hΓ hTf hTa
            obtain ⟨_, _, hEa, _, _, _, _⟩ := iha htra ha' hnb.2 hnfx.2
            exact ⟨.box, vve, .app_box hEf hEa, htrr,
              .box htrr (herapp.defeq henv hΓ hdef), trivial, trivial⟩
          · obtain ⟨fvv0, htrlam0, hfdef⟩ := SEvalβζδ_defeq henv hΔ hcon htrf hf.toSEvalData.toβζδ
            cases htrlam0 with
            | @lam ty' _Δ _ty _body body' _name _bi hty' htrty htrb =>
              obtain ⟨atv, avv, hEa, htrav, herav, hnbatv, hnfatv⟩ := iha htra ha' hnb.2 hnfx.2
              obtain ⟨B'', hbodyT⟩ :=
                TrExprS.wf (Us := Us) (Δ := (none, .vlam ty') :: Δ) henv.ordered
                  ⟨hΔ, nofun, hty'⟩ htrb
              have hAty' : env.IsDefEqU Us.length Δ.toCtx A ty' := by
                obtain ⟨u, hty'sort⟩ := hty'
                have lamT1 : env.HasType Us.length Δ.toCtx (.lam ty' body')
                    (.forallE ty' B'') := VEnv.HasType.lam hty'sort hbodyT
                have lamT2 : env.HasType Us.length Δ.toCtx (.lam ty' body')
                    (.forallE A B) := hTf.defeqU_l henv hΓ hfdef
                obtain ⟨⟨_, h⟩, _⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ
                  (VEnv.IsDefEq.uniqU henv hΓ lamT2 lamT1)
                exact ⟨_, h⟩
              have havIsA : env.IsDefEqU Us.length Δ.toCtx avv a'' := by
                obtain ⟨avv0, htrav0, had0⟩ := SEvalβζδ_defeq henv hΔ hcon htra ha.toSEvalData.toβζδ
                exact VEnv.IsDefEqU.trans henv hΓ
                  (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrav htrav0)
                  (VEnv.IsDefEqU.symm had0)
              have havA : env.HasType Us.length Δ.toCtx avv A :=
                hTa.defeqU_l henv hΓ (VEnv.IsDefEqU.symm havIsA)
              have havT : env.HasType Us.length Δ.toCtx avv ty' :=
                havA.defeqU_r henv hΓ hAty'
              have havTE : env.HasType Us.length Δ.toCtx avv tyE := by
                have : env.IsDefEqU Us.length Δ.toCtx tyE ty' :=
                  TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrtyE htrty
                exact havT.defeqU_r henv hΓ (VEnv.IsDefEqU.symm this)
              have hnbsub : NoBlock (LBTerm.subst1 atv b') :=
                noBlock_subst1 (by simpa [NoBlock] using hnbftv) hnbatv
              have hnfsub : NoFix (LBTerm.subst1 atv b') :=
                noFix_subst1 (by simpa [NoFix] using hnfftv) hnfatv
              obtain ⟨t', vve, hEr, htrr, herr, hnbt', hnft'⟩ := ihbody
                (TrExprS.inst henv.ordered havT htrb htrav)
                (erases_beta_struct henv.ordered htrav havTE hb' herav) hnbsub hnfsub
              exact ⟨t', vve, .beta hEf hEa hEr, htrr, herr, hnbt', hnft'⟩
          · exact hnfftv.elim
      · -- const-headed spine: `.app f a` is a registered ctor/casesOn spine, so its
        -- prefix `f` is a shorter registered spine that cannot evaluate to a λ (by
        -- `SEvalData_const_spine_lam_elim`), contradicting `hf`.
        rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
        · exact absurd hspine (by simp)
        · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons,
            List.foldl_nil] at hspine
          injection hspine with hf_eq _
          exact absurd ⟨n, ty, b, bi, rfl⟩
            (SEvalData_const_spine_lam_elim hnf hf.toSEvalData hf_eq hmem)
  | @delta n us body r hunf hbodyev ihbody =>
      intro ve t htr her hnb hnfx
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      obtain ⟨bve, htrbody, hbdef⟩ := hcon hunf htr
      obtain ⟨hnoctor, _, body', hlook, herbody, hnbbody⟩ := hdelta hunf
      rcases Erases.const_inv her with ⟨veb, htrb, herbox, rfl⟩
        | ⟨kn, hkn, rfl⟩ | ⟨iid, cidx, hctor, rfl⟩
      · obtain ⟨vve, htrr, hrdef⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.delta hunf hbodyev.toSEvalData.toβζδ)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hrdef), trivial, trivial⟩
      · obtain ⟨t', vve, hEbody, htrr, herr, hnbt', hnft'⟩ :=
          ihbody htrbody herbody hnbbody (hnfenv hlook)
        subst hkn
        exact ⟨t', vve, .delta hlook hEbody, htrr, herr, hnbt', hnft'⟩
      · rw [hnoctor] at hctor; exact absurd hctor (by simp)
  | @ctor_val cn us iid cidx ar args vs hcctors har hsat hl hargs ihargs =>
      intro ve t htr her hnb hnfx
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      have harE : constructorArity E iid cidx = some ar := hctorenv hcctors har
      rcases Erases.ctor_spine_inv henv hΔ hcctors (hcc hcctors) args.length args rfl htr her with
        ⟨herve, args', rfl, hmem⟩ | ⟨args', hlen', rfl, hcorr⟩ | hnbt
      · -- box-headed: t = mkApps .box args' ⇓ box; the value is erasable, erases to box
        obtain ⟨vve, htrr, hdef⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.ctor_val hl (fun i h => (hargs i h).toSEvalData.toβζδ))
        have heval : ∀ a' ∈ args', ∃ w, WcbvEval E appliedFlags a' w := by
          intro a' ha'
          obtain ⟨sa, hsa, hera⟩ := hmem a' ha'
          obtain ⟨j, hj, hsaj⟩ := List.mem_iff_getElem.mp hsa
          obtain ⟨sve, htrsa⟩ := (trExprS_appSpine_inv args (.const cn us) ve htr).2 j hj
          obtain ⟨w, _, hEa, _, _, _, _⟩ :=
            ihargs j hj htrsa (hsaj ▸ hera) (noBlock_mkApps_inv hnb a' ha')
              (noFix_mkApps_inv hnfx a' ha')
          exact ⟨w, hEa⟩
        refine ⟨.box, vve, mkApps_headBox_eval WcbvEval.box heval, htrr,
          .box htrr (herve.defeq henv hΓ hdef), trivial, trivial⟩
      · -- headcut: t = mkApps (.construct iid cidx []) args'; A5 accumulates the args
        -- each source arg evaluates via its IH; collect (value, erasure, NoBlock).
        have hpt : ∀ i, i < args.length →
            ∃ w, ∃ (hiA : i < args'.length) (hiV : i < vs.length),
              WcbvEval E appliedFlags (args'[i]'hiA) w ∧
              Erases env Us Γ Δ (vs[i]'hiV) w ∧ NoBlock w ∧ NoFix w := by
          intro i h
          have hiA : i < args'.length := hlen' ▸ h
          have hiV : i < vs.length := hl ▸ h
          obtain ⟨sve, htrsa⟩ := (trExprS_appSpine_inv args (.const cn us) ve htr).2 i h
          have hnba' : NoBlock (args'[i]'hiA) := noBlock_mkApps_inv hnb _ (List.getElem_mem _)
          have hnfa' : NoFix (args'[i]'hiA) := noFix_mkApps_inv hnfx _ (List.getElem_mem _)
          obtain ⟨w, vve, hEa, htrvi, hervi, hnbw, hnfw⟩ :=
            ihargs i h htrsa (hcorr i hiA) hnba' hnfa'
          exact ⟨w, hiA, hiV, hEa, hervi, hnbw, hnfw⟩
        obtain ⟨ws, hwslen, hws⟩ := choose_list args.length hpt
        have hbase : WcbvEval E appliedFlags (.construct iid cidx [])
            (LBTerm.mkApps (.construct iid cidx []) []) := by
          simpa using WcbvEval.construct_atom (Γ := E) (fl := appliedFlags) rfl harE
        have hle : ([] : List LBTerm).length + args'.length ≤ ar := by
          simp only [List.length_nil, Nat.zero_add]; rw [← hlen']; exact hsat
        have hlaw : args'.length = ws.length := by omega
        have hpe : ∀ i (hi : i < args'.length),
            WcbvEval E appliedFlags (args'[i]'hi) (ws[i]'(hlaw ▸ hi)) := by
          intro i hi
          obtain ⟨_, _, hE, _, _, _⟩ := hws i (hlaw ▸ hi)
          exact hE
        have hTeval := construct_app_spine harE args' ws (.construct iid cidx []) [] hbase hle hlaw hpe
        rw [← mkApps_eq_foldl, List.nil_append] at hTeval
        obtain ⟨vve, htrr, _⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.ctor_val hl (fun i h => (hargs i h).toSEvalData.toβζδ))
        have hVerase : Erases env Us Γ Δ (vs.foldl Expr.app (.const cn us))
            (LBTerm.mkApps (.construct iid cidx []) ws) := by
          refine erases_app_spine (.ctor_head cn us iid cidx hcctors) vs ws (by omega) ?_
          intro i hi
          obtain ⟨_, _, _, hEr, _, _⟩ := hws i (by omega)
          exact hEr
        have hVnb : NoBlock (LBTerm.mkApps (.construct iid cidx []) ws) := by
          refine noBlock_mkApps_construct (fun w hw => ?_)
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
          obtain ⟨_, _, _, _, hnbw, _⟩ := hws j hj
          exact hnbw
        have hVnf : NoFix (LBTerm.mkApps (.construct iid cidx []) ws) := by
          refine noFix_mkApps (NoFix_construct iid cidx []) (fun w hw => ?_)
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
          obtain ⟨_, _, _, _, _, hnfw⟩ := hws j hj
          exact hnfw
        exact ⟨_, vve, hTeval, htrr, hVerase, hVnb, hVnf⟩
      · exact absurd hnb hnbt

/-! ## B (ζ case): the vlet-value defeq context transport, and the ζ-including simulation

The ζ case of the data simulation was the one open sub-case of `erases_correct_data`.
The blocker (documented on `SEvalDataC`): source ζ substitutes the **evaluated** value
`vv` into the body, while `erases_subst_let` (nose-preserving) bakes the `vlet`'s
*stored* translation into its substitutee — forcing the substitutee to translate
**exactly** to the stored value, whereas `vv` translates only *up to defeq*. Closing
ζ needs a **depth-generalized `vlet`-value context-defeq transport for `Erases`**:
`Erases.defeqDFC` below moves an `Erases` derivation across a definitionally-equal
`VLCtx` (`VLCtx.IsDefEq`), so the `vlet`'s stored value can be swapped for the
translation of the evaluated value before `erases_subst_let` fires. -/

/-- **Definitionally-equal `VLCtx` transport for `Erases`.** An `Erases` derivation
survives replacing the translation context `Δ₁` by any definitionally-equal `Δ₂`
(`VLCtx.IsDefEq`) — same source `Expr`, same target `LBTerm`. This is the `Erases`
analogue of lean4lean's `TrExprS.defeqDFC`, and the transport the ζ case of the data
simulation needs (to swap a `vlet`'s stored value `val'` for the translation of the
*evaluated* let value, both defeq, ahead of `erases_subst_let`).

The `Erases` rules are context-blind except at the `box`/`lam`/`letE` `TrExprS`
witnesses, which are transported with `TrExprS.defeqDFC'`/`Erasable.defeqDFC`. Because
`Erases.lam`/`.letE` do not themselves certify their binder types are *types*, the
required `IsType`/typed-defeq facts for the extended `VLCtx.IsDefEq` (the `.vlam`/`.vlet`
`VLocalDecl.IsDefEq` obligations) are drawn from a **paired** `TrExprS` derivation
`htyped` of the same source term, whose `lam`/`letE` cases *do* carry them. The
constructor-spine (`ctor`/`cases`) cases recover per-argument typings from `htyped`
via `trExprS_appSpine_inv`. sorry-free (modulo the inherited lean4lean `sorryAx`). -/
theorem Erases.defeqDFC {env : VEnv} (henv : env.WF) {Us : List Name} {Γ : ErasureCtx}
    {Δ₁ Δ₂ : VLCtx} (hΔ : VLCtx.IsDefEq env Us.length Δ₁ Δ₂)
    {e : Expr} {beh : VExpr} (htyped : TrExprS env Us Δ₁ e beh)
    {t : LBTerm} (her : Erases env Us Γ Δ₁ e t) :
    Erases env Us Γ Δ₂ e t := by
  induction her generalizing Δ₂ beh with
  | @box Δ e ve htr her_e =>
      obtain ⟨ve₂, htr₂, hd⟩ := htr.defeqDFC' henv hΔ
      have hΓ₂ : OnCtx Δ₂.toCtx (env.IsType Us.length) := (hΔ.symm henv.ordered).wf.toCtx
      exact .box htr₂ (Erasable.defeq henv hΓ₂ (VEnv.IsDefEqU.symm hd)
        (Erasable.defeqDFC henv.ordered hΔ.defeqCtx her_e))
  | bvar i => exact .bvar i
  | fvar x => exact .fvar x
  | const n us kn h hctor hcases => exact .const n us kn h hctor hcases
  | @app Δ f f' a a' hf ha ihf iha =>
      cases htyped with
      | app _ _ htf hta => exact .app (ihf hΔ htf) (iha hΔ hta)
  | @lam Δ name ty bi b b' ty' hty hb ihb =>
      cases htyped with
      | @lam ty'_t _ _ _ _ _ _ h1 h2 h3 =>
          obtain ⟨ty'', hty''⟩ := hty.defeqDFC henv hΔ
          have hu1 : env.IsDefEqU Us.length Δ.toCtx ty'_t ty' :=
            TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ.wf) h2 hty
          obtain ⟨u, h1'⟩ := h1
          have hty'T : env.HasType Us.length Δ.toCtx ty' (.sort u) :=
            h1'.defeqU_l henv hΔ.wf.toCtx hu1
          have hdef : env.IsDefEq Us.length Δ.toCtx ty' ty'' (.sort u) :=
            (hty.uniq henv hΔ hty'').of_l henv hΔ.wf.toCtx hty'T
          have hΔ' : VLCtx.IsDefEq env Us.length ((none, .vlam ty') :: Δ) ((none, .vlam ty'') :: Δ₂) :=
            hΔ.cons (ofv := none) nofun (.vlam hdef)
          have hΔ3 : VLCtx.IsDefEq env Us.length ((none, .vlam ty'_t) :: Δ) ((none, .vlam ty') :: Δ) :=
            (VLCtx.IsDefEq.refl henv.ordered hΔ.wf).cons (ofv := none) nofun
              (.vlam ((h2.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ.wf) hty).of_l henv hΔ.wf.toCtx h1'))
          obtain ⟨body'', h3'⟩ := h3.defeqDFC henv hΔ3
          exact .lam hty'' (ihb hΔ' h3')
  | @letE Δ name ty nd v v' b b' ty' val' hty hval hv hb ihv ihb =>
      cases htyped with
      | @letE val'_t ty'_t _ _ _ _ body' _ _ hValT h2 h3 h4 =>
          obtain ⟨ty'', hty''⟩ := hty.defeqDFC henv hΔ
          obtain ⟨val'', hval''⟩ := hval.defeqDFC henv hΔ
          have hu_ty : env.IsDefEqU Us.length Δ.toCtx ty'_t ty' :=
            TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ.wf) h2 hty
          have hu_val : env.IsDefEqU Us.length Δ.toCtx val'_t val' :=
            TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ.wf) h3 hval
          have hvalT' : env.HasType Us.length Δ.toCtx val' ty'_t :=
            hValT.defeqU_l henv hΔ.wf.toCtx hu_val
          obtain ⟨uu, hty'T0⟩ := hValT.isType henv hΔ.wf
          have hty'T : env.HasType Us.length Δ.toCtx ty' (.sort uu) :=
            hty'T0.defeqU_l henv hΔ.wf.toCtx hu_ty
          have hvalT : env.HasType Us.length Δ.toCtx val' ty' :=
            hvalT'.defeqU_r henv hΔ.wf.toCtx hu_ty
          have hdef_ty : env.IsDefEq Us.length Δ.toCtx ty' ty'' (.sort uu) :=
            (hty.uniq henv hΔ hty'').of_l henv hΔ.wf.toCtx hty'T
          have hdef_val : env.IsDefEq Us.length Δ.toCtx val' val'' ty' :=
            (hval.uniq henv hΔ hval'').of_l henv hΔ.wf.toCtx hvalT
          have hΔ' : VLCtx.IsDefEq env Us.length ((none, .vlet ty' val') :: Δ) ((none, .vlet ty'' val'') :: Δ₂) :=
            hΔ.cons (ofv := none) nofun (.vlet hdef_val hdef_ty)
          have hdefT_ty : env.IsDefEq Us.length Δ.toCtx ty'_t ty' (.sort uu) :=
            (h2.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ.wf) hty).of_l henv hΔ.wf.toCtx hty'T0
          have hdefT_val : env.IsDefEq Us.length Δ.toCtx val'_t val' ty'_t :=
            (h3.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ.wf) hval).of_l henv hΔ.wf.toCtx hValT
          have hΔ4 : VLCtx.IsDefEq env Us.length ((none, .vlet ty'_t val'_t) :: Δ) ((none, .vlet ty' val') :: Δ) :=
            (VLCtx.IsDefEq.refl henv.ordered hΔ.wf).cons (ofv := none) nofun (.vlet hdefT_val hdefT_ty)
          obtain ⟨body'', h4'⟩ := h4.defeqDFC henv hΔ4
          exact .letE hty'' hval'' (ihv hΔ hval) (ihb hΔ' h4')
  | ctor_head cn us iid cidx hc => exact .ctor_head cn us iid cidx hc
  | @ctor Δ cn us iid cidx args args' hc hlen hargs ihargs =>
      refine .ctor cn us iid cidx hc hlen (fun i hi => ?_)
      obtain ⟨ave, htr_i⟩ := (trExprS_appSpine_inv args (.const cn us) beh htyped).2 i hi
      exact ihargs i hi hΔ htr_i
  | @cases Δ con us iid numParams pre discr discr' minors alts' nfs hc hpre hnfs hd
      hlen hnlen harity halts ihd ihalts =>
      obtain ⟨_, hspine⟩ := trExprS_appSpine_inv (discr :: minors)
        (pre.foldl Expr.app (.const con us)) beh htyped
      obtain ⟨dve, htr_d⟩ := hspine 0 (by simp)
      refine .cases con us iid numParams pre hc hpre hnfs (ihd hΔ (by simpa using htr_d)) hlen
        hnlen harity (fun j hj => ?_)
      obtain ⟨mve, htr_m⟩ := hspine (j + 1) (by simp; omega)
      exact ihalts j hj hΔ (by simpa using htr_m)
  | @fix Δc idx Δf nm tty tb tbi ids osrcs obodies defs hidx holen hblen hilen
      hlift hinst habsl hshift hsubst htobv hclose hbodies _ihb =>
      -- Source/target unchanged by the context defeq; the fix bodies live at the fixed
      -- context `Δf`, so the rule re-applies at the new conclusion context `Δ₂`.
      exact .fix idx hidx holen hblen hilen hlift hinst habsl hshift hsubst htobv hclose hbodies

/-- **Erasure correctness — forward simulation, β + ζ + δ + saturated constructors,
at MetaRocq's non-block `appliedFlags`.** The ζ-including data-fragment simulation:
identical to `erases_correct_data` but over the full `SEvalData` (β+ζ+δ+ctor, adding
the `zeta` case). Chosen **additive** form (i): `erases_correct_data`'s signature is
untouched (P2 keeps consuming it); this is a separate theorem over the strictly larger
`SEvalData`.

The `zeta` case: `IH(v)` evaluates the let value `v'` to `vtv` (erasing `vv`); the
reduct erasure `Erases Δ (b[vv]) (subst1 vtv b')` is built by transporting the body
erasure `hb` from the `vlet` storing `val'` to one storing the translation of `vv`
(`Erases.defeqDFC`, using subject reduction `val' ≡ ⟦vv⟧`) and then `erases_subst_let`;
its `TrExprS` comes from `TrExpr.inst_let`; `IH(b[vv])` closes it, and `WcbvEval.zeta`
assembles the target `letIn` step. Same threaded consistency hypotheses as
`erases_correct_data`. -/
theorem erases_correct_data_zeta {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {Γ : ErasureCtx} {Esrc : SEnv} {E : GlobalDeclarations}
    (hcon : SEnvConsistent env Us Esrc)
    (hdelta : ErasesEnvDeltaData env Us Γ Esrc E)
    (hctorenv : ErasesEnvCtor Γ E)
    (hcc : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
             Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none)
    (hnfenv : NoFixEnv E)
    {e v : Expr} (hev : SEvalData Γ Esrc e v) :
    ∀ {ve : VExpr} {t : LBTerm},
      TrExprS env Us Δ e ve → Erases env Us Γ Δ e t → NoBlock t → NoFix t →
      ∃ t' vve, WcbvEval E appliedFlags t t' ∧ TrExprS env Us Δ v vve ∧
        Erases env Us Γ Δ v t' ∧ NoBlock t' ∧ NoFix t' := by
  have hnf : ∀ {n : Name} {body : Expr}, Esrc n = some body →
      Γ.ctors n = none ∧ Γ.casesOns n = none :=
    fun h => ⟨(hdelta (Δ := Δ) h).1, (hdelta (Δ := Δ) h).2.1⟩
  induction hev with
  | lam n ty b bi =>
      intro ve t htr her hnb hnfx
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      rcases Erases.lam_inv her with ⟨veb, htrb, herbox, rfl⟩ | ⟨_, _, hty, hb, rfl⟩
        | ⟨defs, idx, rfl, _⟩
      · exact ⟨.box, ve, .box, htr, .box htr
          (herbox.defeq henv hΓ
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)), trivial, trivial⟩
      · exact ⟨_, ve, .lam _ _, htr, .lam hty hb, hnb, hnfx⟩
      · exact hnfx.elim
  | @beta f a n ty b bi av r hf ha hbody ihf iha ihbody =>
      intro ve t htr her hnb hnfx
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      rcases Erases.app_inv her with
        ⟨veb, htrb, herbox, rfl⟩ | ⟨f't, a't, hf', ha', rfl⟩ | ⟨cn, us, args, hspine, hmem⟩
      · obtain ⟨vve, htrr, hdef⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.beta hf.toβζδ ha.toβζδ hbody.toβζδ)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hdef), trivial, trivial⟩
      · cases htr with
        | @app f' A B a'' _Δ _f _a hTf hTa htrf htra =>
          obtain ⟨ftv, fvv, hEf, htrlam, herlam, hnbftv, hnfftv⟩ := ihf htrf hf' hnb.1 hnfx.1
          rcases Erases.lam_inv herlam with ⟨velam, htrvelam, herlamE, rfl⟩
            | ⟨tyE, b', htrtyE, hb', rfl⟩ | ⟨defs, idx, rfl, _⟩
          · obtain ⟨vve, htrr, hdef⟩ :=
              SEvalβζδ_defeq henv hΔ hcon (.app hTf hTa htrf htra)
                (.beta hf.toβζδ ha.toβζδ hbody.toβζδ)
            obtain ⟨fvv0, htrlam0, hfdef⟩ := SEvalβζδ_defeq henv hΔ hcon htrf hf.toβζδ
            have hferase : Erasable env Us.length Δ.toCtx f' :=
              (herlamE.defeq henv hΓ
                (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrvelam htrlam0)).defeq
                henv hΓ (VEnv.IsDefEqU.symm hfdef)
            have herapp : Erasable env Us.length Δ.toCtx (.app f' a'') :=
              hferase.app henv hΓ hTf hTa
            obtain ⟨_, _, hEa, _, _, _, _⟩ := iha htra ha' hnb.2 hnfx.2
            exact ⟨.box, vve, .app_box hEf hEa, htrr,
              .box htrr (herapp.defeq henv hΓ hdef), trivial, trivial⟩
          · obtain ⟨fvv0, htrlam0, hfdef⟩ := SEvalβζδ_defeq henv hΔ hcon htrf hf.toβζδ
            cases htrlam0 with
            | @lam ty' _Δ _ty _body body' _name _bi hty' htrty htrb =>
              obtain ⟨atv, avv, hEa, htrav, herav, hnbatv, hnfatv⟩ := iha htra ha' hnb.2 hnfx.2
              obtain ⟨B'', hbodyT⟩ :=
                TrExprS.wf (Us := Us) (Δ := (none, .vlam ty') :: Δ) henv.ordered
                  ⟨hΔ, nofun, hty'⟩ htrb
              have hAty' : env.IsDefEqU Us.length Δ.toCtx A ty' := by
                obtain ⟨u, hty'sort⟩ := hty'
                have lamT1 : env.HasType Us.length Δ.toCtx (.lam ty' body')
                    (.forallE ty' B'') := VEnv.HasType.lam hty'sort hbodyT
                have lamT2 : env.HasType Us.length Δ.toCtx (.lam ty' body')
                    (.forallE A B) := hTf.defeqU_l henv hΓ hfdef
                obtain ⟨⟨_, h⟩, _⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ
                  (VEnv.IsDefEq.uniqU henv hΓ lamT2 lamT1)
                exact ⟨_, h⟩
              have havIsA : env.IsDefEqU Us.length Δ.toCtx avv a'' := by
                obtain ⟨avv0, htrav0, had0⟩ := SEvalβζδ_defeq henv hΔ hcon htra ha.toβζδ
                exact VEnv.IsDefEqU.trans henv hΓ
                  (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrav htrav0)
                  (VEnv.IsDefEqU.symm had0)
              have havA : env.HasType Us.length Δ.toCtx avv A :=
                hTa.defeqU_l henv hΓ (VEnv.IsDefEqU.symm havIsA)
              have havT : env.HasType Us.length Δ.toCtx avv ty' :=
                havA.defeqU_r henv hΓ hAty'
              have havTE : env.HasType Us.length Δ.toCtx avv tyE := by
                have : env.IsDefEqU Us.length Δ.toCtx tyE ty' :=
                  TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrtyE htrty
                exact havT.defeqU_r henv hΓ (VEnv.IsDefEqU.symm this)
              have hnbsub : NoBlock (LBTerm.subst1 atv b') :=
                noBlock_subst1 (by simpa [NoBlock] using hnbftv) hnbatv
              have hnfsub : NoFix (LBTerm.subst1 atv b') :=
                noFix_subst1 (by simpa [NoFix] using hnfftv) hnfatv
              obtain ⟨t', vve, hEr, htrr, herr, hnbt', hnft'⟩ := ihbody
                (TrExprS.inst henv.ordered havT htrb htrav)
                (erases_beta_struct henv.ordered htrav havTE hb' herav) hnbsub hnfsub
              exact ⟨t', vve, .beta hEf hEa hEr, htrr, herr, hnbt', hnft'⟩
          · exact hnfftv.elim
      · rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
        · exact absurd hspine (by simp)
        · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons,
            List.foldl_nil] at hspine
          injection hspine with hf_eq _
          exact absurd ⟨n, ty, b, bi, rfl⟩
            (SEvalData_const_spine_lam_elim hnf hf hf_eq hmem)
  | @zeta n ty v b nd vv r hval_ev hbody_ev ihval ihbody =>
      intro ve t htr her hnb hnfx
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      rcases Erases.letE_inv her with ⟨veb, htrb, herbox, rfl⟩
        | ⟨ty'ₑ, val'ₑ, v', b', hty_e, hval_e, hv_er, hb_er, rfl⟩
      · obtain ⟨vve, htrr, hdef⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.zeta hval_ev.toβζδ hbody_ev.toβζδ)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hdef), trivial, trivial⟩
      · cases htr with
        | @letE val'_T ty'_T _ _ _ _ _ _ _ hValT htrty_T htrval_T htrb_T =>
          obtain ⟨vtv, vvve, hEv, htr_vv, her_vv, hnb_vtv, hnf_vtv⟩ :=
            ihval hval_e hv_er hnb.1 hnfx.1
          obtain ⟨vvve', htr_vv', hval_defeq⟩ :=
            SEvalβζδ_defeq henv hΔ hcon hval_e hval_ev.toβζδ
          have hval_eq_vvve : env.IsDefEqU Us.length Δ.toCtx val'ₑ vvve :=
            VEnv.IsDefEqU.trans henv hΓ hval_defeq
              (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htr_vv' htr_vv)
          have hu_ty : env.IsDefEqU Us.length Δ.toCtx ty'_T ty'ₑ :=
            TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrty_T hty_e
          have hu_val : env.IsDefEqU Us.length Δ.toCtx val'_T val'ₑ :=
            TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrval_T hval_e
          obtain ⟨uu, hty'T0⟩ := hValT.isType henv hΔ
          have hty'ₑT : env.HasType Us.length Δ.toCtx ty'ₑ (.sort uu) :=
            hty'T0.defeqU_l henv hΓ hu_ty
          have hval'ₑT : env.HasType Us.length Δ.toCtx val'ₑ ty'ₑ :=
            (hValT.defeqU_l henv hΓ hu_val).defeqU_r henv hΓ hu_ty
          have hdef_val : env.IsDefEq Us.length Δ.toCtx val'ₑ vvve ty'ₑ :=
            VEnv.IsDefEqU.of_l henv hΓ hval_eq_vvve hval'ₑT
          have hΔvlet : VLCtx.IsDefEq env Us.length
              ((none, .vlet ty'ₑ val'ₑ) :: Δ) ((none, .vlet ty'ₑ vvve) :: Δ) :=
            (VLCtx.IsDefEq.refl henv.ordered hΔ).cons (ofv := none) nofun
              (.vlet hdef_val hty'ₑT)
          have hΔbT : VLCtx.IsDefEq env Us.length
              ((none, .vlet ty'_T val'_T) :: Δ) ((none, .vlet ty'ₑ val'ₑ) :: Δ) :=
            (VLCtx.IsDefEq.refl henv.ordered hΔ).cons (ofv := none) nofun
              (.vlet (VEnv.IsDefEqU.of_l henv hΓ hu_val hValT)
                (VEnv.IsDefEqU.of_l henv hΓ hu_ty hty'T0))
          obtain ⟨behb, htyped_b⟩ := htrb_T.defeqDFC henv hΔbT
          have hb_er_vvve : Erases env Us Γ ((none, .vlet ty'ₑ vvve) :: Δ) b b' :=
            Erases.defeqDFC henv hΔvlet htyped_b hb_er
          have hb_reduct_er : Erases env Us Γ Δ (b.instantiate1' vv 0) (LBTerm.subst1 vtv b') :=
            erases_subst_let henv.ordered htr_vv her_vv (.zero) hb_er_vvve
          obtain ⟨vvT, htr_vvT, hvaldefT⟩ :=
            SEvalβζδ_defeq henv hΔ hcon htrval_T hval_ev.toβζδ
          have hΔlet : VLCtx.WF env Us.length ((none, .vlet ty'_T val'_T) :: Δ) :=
            ⟨hΔ, nofun, hValT⟩
          have hbodyTrExpr : TrExpr env Us ((none, .vlet ty'_T val'_T) :: Δ) b ve :=
            ⟨ve, htrb_T, VEnv.IsDefEqU.refl (htrb_T.wf henv.ordered hΔlet)⟩
          have hvvTrExpr : TrExpr env Us Δ vv val'_T :=
            ⟨vvT, htr_vvT, VEnv.IsDefEqU.symm hvaldefT⟩
          obtain ⟨sub', htr_sub, hsubd⟩ :=
            TrExpr.inst_let henv hΔ hValT hbodyTrExpr hvvTrExpr
          have hnb_reduct : NoBlock (LBTerm.subst1 vtv b') :=
            noBlock_subst1 hnb.2 hnb_vtv
          have hnf_reduct : NoFix (LBTerm.subst1 vtv b') :=
            noFix_subst1 hnfx.2 hnf_vtv
          obtain ⟨t', vve, hEr', htrr, herr, hnbt', hnft'⟩ :=
            ihbody htr_sub hb_reduct_er hnb_reduct hnf_reduct
          exact ⟨t', vve, .zeta hEv hEr', htrr, herr, hnbt', hnft'⟩
  | @delta n us body r hunf hbodyev ihbody =>
      intro ve t htr her hnb hnfx
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      obtain ⟨bve, htrbody, hbdef⟩ := hcon hunf htr
      obtain ⟨hnoctor, _, body', hlook, herbody, hnbbody⟩ := hdelta hunf
      rcases Erases.const_inv her with ⟨veb, htrb, herbox, rfl⟩
        | ⟨kn, hkn, rfl⟩ | ⟨iid, cidx, hctor, rfl⟩
      · obtain ⟨vve, htrr, hrdef⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.delta hunf hbodyev.toβζδ)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hrdef), trivial, trivial⟩
      · obtain ⟨t', vve, hEbody, htrr, herr, hnbt', hnft'⟩ :=
          ihbody htrbody herbody hnbbody (hnfenv hlook)
        subst hkn
        exact ⟨t', vve, .delta hlook hEbody, htrr, herr, hnbt', hnft'⟩
      · rw [hnoctor] at hctor; exact absurd hctor (by simp)
  | @ctor_val cn us iid cidx ar args vs hcctors har hsat hl hargs ihargs =>
      intro ve t htr her hnb hnfx
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      have harE : constructorArity E iid cidx = some ar := hctorenv hcctors har
      rcases Erases.ctor_spine_inv henv hΔ hcctors (hcc hcctors) args.length args rfl htr her with
        ⟨herve, args', rfl, hmem⟩ | ⟨args', hlen', rfl, hcorr⟩ | hnbt
      · obtain ⟨vve, htrr, hdef⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.ctor_val hl (fun i h => (hargs i h).toβζδ))
        have heval : ∀ a' ∈ args', ∃ w, WcbvEval E appliedFlags a' w := by
          intro a' ha'
          obtain ⟨sa, hsa, hera⟩ := hmem a' ha'
          obtain ⟨j, hj, hsaj⟩ := List.mem_iff_getElem.mp hsa
          obtain ⟨sve, htrsa⟩ := (trExprS_appSpine_inv args (.const cn us) ve htr).2 j hj
          obtain ⟨w, _, hEa, _, _, _, _⟩ :=
            ihargs j hj htrsa (hsaj ▸ hera) (noBlock_mkApps_inv hnb a' ha')
              (noFix_mkApps_inv hnfx a' ha')
          exact ⟨w, hEa⟩
        refine ⟨.box, vve, mkApps_headBox_eval WcbvEval.box heval, htrr,
          .box htrr (herve.defeq henv hΓ hdef), trivial, trivial⟩
      · have hpt : ∀ i, i < args.length →
            ∃ w, ∃ (hiA : i < args'.length) (hiV : i < vs.length),
              WcbvEval E appliedFlags (args'[i]'hiA) w ∧
              Erases env Us Γ Δ (vs[i]'hiV) w ∧ NoBlock w ∧ NoFix w := by
          intro i h
          have hiA : i < args'.length := hlen' ▸ h
          have hiV : i < vs.length := hl ▸ h
          obtain ⟨sve, htrsa⟩ := (trExprS_appSpine_inv args (.const cn us) ve htr).2 i h
          have hnba' : NoBlock (args'[i]'hiA) := noBlock_mkApps_inv hnb _ (List.getElem_mem _)
          have hnfa' : NoFix (args'[i]'hiA) := noFix_mkApps_inv hnfx _ (List.getElem_mem _)
          obtain ⟨w, vve, hEa, htrvi, hervi, hnbw, hnfw⟩ :=
            ihargs i h htrsa (hcorr i hiA) hnba' hnfa'
          exact ⟨w, hiA, hiV, hEa, hervi, hnbw, hnfw⟩
        obtain ⟨ws, hwslen, hws⟩ := choose_list args.length hpt
        have hbase : WcbvEval E appliedFlags (.construct iid cidx [])
            (LBTerm.mkApps (.construct iid cidx []) []) := by
          simpa using WcbvEval.construct_atom (Γ := E) (fl := appliedFlags) rfl harE
        have hle : ([] : List LBTerm).length + args'.length ≤ ar := by
          simp only [List.length_nil, Nat.zero_add]; rw [← hlen']; exact hsat
        have hlaw : args'.length = ws.length := by omega
        have hpe : ∀ i (hi : i < args'.length),
            WcbvEval E appliedFlags (args'[i]'hi) (ws[i]'(hlaw ▸ hi)) := by
          intro i hi
          obtain ⟨_, _, hE, _, _, _⟩ := hws i (hlaw ▸ hi)
          exact hE
        have hTeval := construct_app_spine harE args' ws (.construct iid cidx []) [] hbase hle hlaw hpe
        rw [← mkApps_eq_foldl, List.nil_append] at hTeval
        obtain ⟨vve, htrr, _⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.ctor_val hl (fun i h => (hargs i h).toβζδ))
        have hVerase : Erases env Us Γ Δ (vs.foldl Expr.app (.const cn us))
            (LBTerm.mkApps (.construct iid cidx []) ws) := by
          refine erases_app_spine (.ctor_head cn us iid cidx hcctors) vs ws (by omega) ?_
          intro i hi
          obtain ⟨_, _, _, hEr, _, _⟩ := hws i (by omega)
          exact hEr
        have hVnb : NoBlock (LBTerm.mkApps (.construct iid cidx []) ws) := by
          refine noBlock_mkApps_construct (fun w hw => ?_)
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
          obtain ⟨_, _, _, _, hnbw, _⟩ := hws j hj
          exact hnbw
        have hVnf : NoFix (LBTerm.mkApps (.construct iid cidx []) ws) := by
          refine noFix_mkApps (NoFix_construct iid cidx []) (fun w hw => ?_)
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
          obtain ⟨_, _, _, _, _, hnfw⟩ := hws j hj
          exact hnfw
        exact ⟨_, vve, hTeval, htrr, hVerase, hVnb, hVnf⟩
      · exact absurd hnb hnbt

end LeanToLambdaBox
