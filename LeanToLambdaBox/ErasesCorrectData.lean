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
non-block spine, MetaRocq's `atom (tConstruct ind c [])`) is allowed. `proj` is treated
opaquely (`True`) — the data fragment of `erases_correct_data` never produces one.

`.case` **is** traversed (ι Task 3): the ι forward simulation
(`ErasesCorrectIota.lean`) inverts a target `.case (iid, np) discr' alts'` and must feed
`NoBlock discr'` to the discriminant IH and `NoBlock (alts'[cidx]).2` to the branch IH.
With a `True` clause neither is obtainable and the ι case cannot be started at all. The
per-alternative traversal goes through the mutual helper `NoBlockAlts` (the nested-list
occurrence defeats the structural-recursion checker in `∀ a ∈ alts, NoBlock a.2` form);
`NoBlock_case`/`NoBlockAlts_iff` expose exactly that form.

`.fix` **is** traversed too (recursion wall, slice W0), for the same reason one step
later: once the simulations accept `.fix` targets, the β case's target step is
`WcbvEval.fix_guarded`, whose reduct is
`.app (substList (fixSubst defs) defs[idx].body) av` — so the induction must carry
`NoBlock` *through a fix unfolding*, and that is underivable from an opaque `True`
clause (the unfolded body is `defs[idx].body` with `.fix defs j` substituted in, and
both halves need the predicate). The traversal mirrors `LBClosedDefs` (`Closed.lean`)
via the mutual helper `NoBlockDefs`, with `NoBlock_fix`/`NoBlockDefs_iff` exposing the
per-definition form. Note `NoFix` needs no such change: it is `False` on `.fix` by
construction, so there is nothing to traverse.

All existing consumers use `NoBlock` in hypothesis position, or in `¬ NoBlock`
(conclusion) position, or conclude it for `box`/`construct`-spine/`lambda`/`subst1`/
`mkLambdas`/IH witnesses — never for a `.fix` head — so both strengthenings are free
for them. -/
mutual
def NoBlock : LBTerm → Prop
  | .lambda _ b => NoBlock b
  | .letIn _ v b => NoBlock v ∧ NoBlock b
  | .app f a => NoBlock f ∧ NoBlock a
  | .case _ d alts => NoBlock d ∧ NoBlockAlts alts
  | .fix defs _ => NoBlockDefs defs
  | .construct _ _ [] => True
  | .construct _ _ (_ :: _) => False
  | .box => True
  | .bvar _ => True
  | .fvar _ => True
  | .const _ => True
  | .proj _ _ => True
  | .prim _ => True

/-- `NoBlock` over `case` alternatives (each branch body is `NoBlock`). -/
def NoBlockAlts : List (List BinderName × LBTerm) → Prop
  | [] => True
  | (_, b) :: rest => NoBlock b ∧ NoBlockAlts rest

/-- `NoBlock` over `fix` definitions (each definition body is `NoBlock`). -/
def NoBlockDefs : List (@FixDef LBTerm) → Prop
  | [] => True
  | fd :: rest => NoBlock fd.body ∧ NoBlockDefs rest
end

/-- `NoBlockAlts` in the natural per-element form. -/
theorem NoBlockAlts_iff (l : List (List BinderName × LBTerm)) :
    NoBlockAlts l ↔ ∀ a ∈ l, NoBlock a.2 := by
  induction l with
  | nil => simp [NoBlockAlts]
  | cons a rest ih => obtain ⟨ns, b⟩ := a; simp [NoBlockAlts, ih]

/-- `NoBlockDefs` in the natural per-element form. -/
theorem NoBlockDefs_iff (l : List (@FixDef LBTerm)) :
    NoBlockDefs l ↔ ∀ d ∈ l, NoBlock d.body := by
  induction l with
  | nil => simp [NoBlockDefs]
  | cons fd rest ih => simp [NoBlockDefs, ih]

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
@[simp] theorem NoBlock_case (info : InductiveId × Nat) (d : LBTerm)
    (alts : List (List BinderName × LBTerm)) :
    NoBlock (.case info d alts) ↔ NoBlock d ∧ ∀ a ∈ alts, NoBlock a.2 := by
  show NoBlock d ∧ NoBlockAlts alts ↔ _
  rw [NoBlockAlts_iff]
@[simp] theorem NoBlock_proj (p : ProjectionInfo) (e : LBTerm) : NoBlock (.proj p e) := trivial
@[simp] theorem NoBlock_fix (defs : List (@FixDef LBTerm)) (i : Nat) :
    NoBlock (.fix defs i) ↔ ∀ d ∈ defs, NoBlock d.body := by
  show NoBlockDefs defs ↔ _
  rw [NoBlockDefs_iff]
@[simp] theorem NoBlock_prim (p : PrimVal) : NoBlock (.prim p) := trivial

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
  | hcase info discr alts ihd iha =>
      rw [NoBlock_case] at hs
      simp only [LBTerm.shift, NoBlock_case, LBTerm.shiftAlts_eq_map]
      refine ⟨ihd hs.1 c, fun a ha => ?_⟩
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact iha b hb (hs.2 b hb) _
  | hfix defs i ih =>
      rw [NoBlock_fix] at hs
      simp only [LBTerm.shift, NoBlock_fix, LBTerm.shiftDefs_eq_map]
      intro fd hfd
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hfd
      exact ih y hy (hs y hy) _
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
  | hcase info discr alts ihd iha =>
      rw [NoBlock_case] at ht
      simp only [LBTerm.subst, NoBlock_case, LBTerm.substAlts_eq_map]
      refine ⟨ihd ht.1 d, fun a ha => ?_⟩
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact iha b hb (ht.2 b hb) _
  | hfix defs i ih =>
      rw [NoBlock_fix] at ht
      simp only [LBTerm.subst, NoBlock_fix, LBTerm.substDefs_eq_map]
      intro fd hfd
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hfd
      exact ih y hy (ht y hy) _
  | _ => trivial

theorem noBlock_subst1 {t s : LBTerm} (ht : NoBlock t) (hs : NoBlock s) :
    NoBlock (LBTerm.subst1 s t) := noBlock_subst ht hs 0

/-- `NoBlock` is preserved by simultaneous substitution. -/
theorem noBlock_substList {ss : List LBTerm} (hs : ∀ s ∈ ss, NoBlock s) :
    ∀ {t : LBTerm}, NoBlock t → NoBlock (LBTerm.substList ss t) := by
  induction ss with
  | nil => exact fun ht => ht
  | cons a as ih =>
      intro t ht
      exact ih (fun s hsm => hs s (List.mem_cons_of_mem _ hsm))
        (noBlock_subst1 ht (hs a (List.mem_cons_self ..)))

/-- Every entry of `fixSubst defs` is `.fix defs j` for some `j`, and `NoBlock` of a
`.fix` node does not depend on the index — so a `NoBlock` fix block has a `NoBlock`
unfolding substitution. -/
theorem noBlock_fixSubst {defs : List (@FixDef LBTerm)} {i : Nat}
    (h : NoBlock (.fix defs i)) : ∀ s ∈ LBTerm.fixSubst defs, NoBlock s := by
  rw [NoBlock_fix] at h
  intro s hsm
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hsm
  rw [NoBlock_fix]
  exact h

/-- **`NoBlock` survives a `fix` unfolding.** This is what the β case of the forward
simulations needs once `.fix` targets are admitted: `WcbvEval.fix_guarded`'s reduct is
`.app (mkApps (substList (fixSubst defs) def_i.body) argsv) av`, and its head must stay
in the applied (non-block) fragment for the induction to continue. Underivable while
`NoBlock` was opaque on `.fix` — that is the whole reason for the `NoBlockDefs`
traversal above. -/
theorem noBlock_fixUnfold {defs : List (@FixDef LBTerm)} {i : Nat}
    {def_i : @FixDef LBTerm} (h : NoBlock (.fix defs i)) (hsel : defs[i]? = some def_i) :
    NoBlock (LBTerm.substList (LBTerm.fixSubst defs) def_i.body) := by
  refine noBlock_substList (noBlock_fixSubst h) ?_
  rw [NoBlock_fix] at h
  exact h def_i (List.mem_of_getElem? hsel)

/-- **`NoBlock` survives a whole unfolding chain** (recursion wall, slice W2) — the
`P := NoBlock` instance of `erases_lam_head_step`'s `hPchain`. -/
theorem FixUnfoldChain.noBlock {defs : List (@FixDef LBTerm)} {idx : Nat} {u : LBTerm}
    (hch : FixUnfoldChain defs idx u) : NoBlock (.fix defs idx) → NoBlock u := by
  induction hch with
  | step hidx _ => exact fun h => noBlock_fixUnfold h (List.getElem?_eq_getElem hidx)
  | trans hidx _ heq _ ih =>
      exact fun h => ih (heq ▸ noBlock_fixUnfold h (List.getElem?_eq_getElem hidx))

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

/-- The argument list of a source application spine, in order — the `Expr` mirror of
`LBTerm.spineArgs`. Together with `expr_getAppFn_foldl` it gives injectivity of a
`.const`-headed `foldl` spine (`foldl_app_const_inj`), which is what lets the `cases`
rule's own `pre ++ discr :: minors` decomposition be matched against an ambient
positional one. -/
def exprSpineArgs : Expr → List Expr
  | .app f a => exprSpineArgs f ++ [a]
  | _ => []

theorem exprSpineArgs_foldl (f : Expr) : ∀ (l : List Expr),
    exprSpineArgs (l.foldl Expr.app f) = exprSpineArgs f ++ l := by
  intro l
  induction l generalizing f with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons, ih (f.app a), exprSpineArgs]; simp

/-- **Injectivity of a `.const`-headed application spine.** Two `foldl` spines over
constant heads are equal only if head, universes and argument list all agree. -/
theorem foldl_app_const_inj {c₁ c₂ : Name} {u₁ u₂ : List Level} {l₁ l₂ : List Expr}
    (h : l₁.foldl Expr.app (.const c₁ u₁) = l₂.foldl Expr.app (.const c₂ u₂)) :
    c₁ = c₂ ∧ u₁ = u₂ ∧ l₁ = l₂ := by
  have hl : l₁ = l₂ := by
    have := congrArg exprSpineArgs h
    simpa only [exprSpineArgs_foldl, exprSpineArgs, List.nil_append] using this
  subst hl
  have hfn := congrArg Expr.getAppFn h
  rw [expr_getAppFn_foldl, expr_getAppFn_foldl] at hfn
  simp only [Expr.getAppFn] at hfn
  injection hfn with h1 h2
  exact ⟨h1, h2, rfl⟩

/-- **t-preserving inversion of `Erases` on an application node.** Unlike
`Erases.app_inv`, the block-`ctor` and `cases` disjuncts retain the target `t`
(needed by A6 to detect the block form).

The `cases` disjunct returns the rule's **full** payload — the three T1 arity pins
(`hpre`/`hnfs`+`hnlen`/`harity`), the discriminant erasure and the per-minor erasures —
not just the head registration. `Erases.cases_spine_inv` (A6ι) needs every one of them
to reconstruct a positional split of the spine; the earlier weak form discarded exactly
the data T1 landed. -/
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
        (alts' : List (List BinderName × LBTerm)) (nfs : List Nat),
        Expr.app f a = (discr :: minors).foldl Expr.app (pre.foldl Expr.app (.const con us)) ∧
        Γ.casesOns con = some (iid, np) ∧
        Γ.casesDiscrPos con = some pre.length ∧
        Γ.ctorFields iid = some nfs ∧
        Erases env Us Γ Δ discr discr' ∧
        ∃ (hlen : minors.length = alts'.length) (hnlen : alts'.length = nfs.length),
          (∀ j (hj : j < alts'.length), (alts'[j]'hj).1.length = nfs[j]'(hnlen ▸ hj)) ∧
          (∀ j (hj : j < minors.length), Erases env Us Γ Δ minors[j]
              (mkLambdas (alts'[j]'(hlen ▸ hj)).1 (alts'[j]'(hlen ▸ hj)).2)) ∧
          t = .case (iid, np) discr' alts') := by
  generalize he : (Expr.app f a) = e₀ at h
  induction h with
  | box htr' her' => subst he; exact .inl ⟨_, htr', her', rfl⟩
  | app hf ha => cases he; exact .inr (.inl ⟨_, _, hf, ha, rfl⟩)
  | @ctor _ cn us iid cidx args args' hc hlen _ _ =>
      exact .inr (.inr (.inl ⟨cn, us, args, iid, cidx, args', rfl, hc, hlen, rfl⟩))
  | @cases _ con us iid np pre discr discr' minors alts' nfs hcase hpre hnfs hd
      hlen hnlen harity halts _ _ =>
      exact .inr (.inr (.inr ⟨con, us, pre, discr, minors, iid, np, discr', alts', nfs,
        rfl, hcase, hpre, hnfs, hd, hlen, hnlen, harity, halts, rfl⟩))
  | _ => exact absurd he (by simp)

/-- **`.const`-source inversion keeping the `ctors`/`casesOns = none` witnesses** (which
`const_inv` discards) — needed to exclude the plain-`const` rule on a registered
constructor head (`ctors`) or a registered `casesOn` head (`casesOns`, the base case of
`Erases.cases_spine_inv`). Since the recursion wall's `const_fix` and `fixvar` leaves
there are a fourth and a fifth disjunct, and both keep the same two witnesses: that is
exactly what lets the spine inversions below refute them at a registered head, with no
new premise. -/
theorem Erases.const_inv_full {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx}
    {n : Name} {us : List Level} {t : LBTerm} (h : Erases env Us Γ Δ (.const n us) t) :
    (∃ ve, TrExprS env Us Δ (.const n us) ve ∧
        Erasable env Us.length Δ.toCtx ve ∧ t = .box) ∨
    (∃ kn, Γ.constants n = kn ∧ Γ.ctors n = none ∧ Γ.casesOns n = none ∧ t = .const kn) ∨
    (∃ (iid : InductiveId) (cidx : Nat), Γ.ctors n = some (iid, cidx) ∧
        t = .construct iid cidx []) ∨
    (∃ (defs : List (@FixDef LBTerm)) (idx : Nat), Γ.recBodies n = some (defs, idx) ∧
        Γ.ctors n = none ∧ Γ.casesOns n = none ∧ t = .fix defs idx) ∨
    (∃ x : FVarId, Γ.fixvars n = some x ∧
        Γ.ctors n = none ∧ Γ.casesOns n = none ∧ t = .fvar x) := by
  generalize he : (Expr.const n us) = e₀ at h
  induction h with
  | box htr' her' => subst he; exact .inl ⟨_, htr', her', rfl⟩
  | const m ms kn hkn hctor hcases => cases he; exact .inr (.inl ⟨_, hkn, hctor, hcases, rfl⟩)
  | ctor_head cn cus iid cidx hc => cases he; exact .inr (.inr (.inl ⟨iid, cidx, hc, rfl⟩))
  | const_fix m ms hrec hctor hcases _ _ _ =>
      cases he; exact .inr (.inr (.inr (.inl ⟨_, _, hrec, hctor, hcases, rfl⟩)))
  | fixvar m ms x hfx hctor hcases _ =>
      cases he; exact .inr (.inr (.inr (.inr ⟨_, hfx, hctor, hcases, rfl⟩)))
  | @ctor _ cn cus iid cidx args args' hc hlen _ _ =>
      rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
      · simp only [List.foldl] at he
        cases he
        have : args' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
        subst this
        exact .inr (.inr (.inl ⟨iid, cidx, hc, rfl⟩))
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
      rcases her.const_inv_full with ⟨ve', htr', her', rfl⟩ | ⟨kn, _, hctor, _, rfl⟩
        | ⟨iid2, cidx2, hc2, rfl⟩ | ⟨defs, fidx, _, hctor, _, rfl⟩ | ⟨x, _, hctor, _, rfl⟩
      · refine .inl ⟨?_, [], rfl, by simp⟩
        exact her'.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htr' htr)
      · rw [hc] at hctor; exact absurd hctor (by simp)
      · rw [hc] at hc2; injection hc2 with hpair; injection hpair with h1 h2; subst h1; subst h2
        exact .inr (.inl ⟨[], rfl, by simp [LBTerm.mkApps], fun i h => absurd h (by simp)⟩)
      · -- `const_fix` at a *registered constructor* head: refuted by the leaf's own
        -- `Γ.ctors = none` witness.
        rw [hc] at hctor; exact absurd hctor (by simp)
      · -- `fixvar` at a *registered constructor* head: same witness, same refutation.
        rw [hc] at hctor; exact absurd hctor (by simp)
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
          ⟨con, us2, pre, discr, minors, iid2, np, discr', alts', nfs2, hsrc, hcase2,
            _, _, _, _, _, _, _, rfl⟩
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

/-! ## A6ι: classifying the erasure of a `casesOn` application spine

`Erases.cases_spine_inv` is the `casesOn` counterpart of `ctor_spine_inv`, and the
inversion the ι forward simulation (`ErasesCorrectIota.lean`) runs on its redex. It is
formulated **positionally** — every payload is indexed off the ambient `args` list rather
than off a rule-supplied `pre`/`discr`/`minors` decomposition — deliberately mirroring
T4's `Supported.casesApp_inv`, so that the shipping-side and relation-side inversions
index the same spine the same way and their composition (Task 5) is mechanical. -/

/-- `List.eq_nil_or_concat` with the tail spelled as an append: rewriting a `concat`
under a dependent `getElem` proof breaks the motive, and `cases_spine_inv`'s payload is
position-indexed throughout. (T4's `list_eq_nil_or_append_singleton` is the same lemma;
duplicated rather than imported because `VisitExprRefines` sits far downstream of this
file.) -/
theorem list_nil_or_snoc {α : Type _} (l : List α) :
    l = [] ∨ ∃ (init : List α) (last : α), l = init ++ [last] := by
  rcases List.eq_nil_or_concat l with rfl | ⟨init, last, rfl⟩
  · exact .inl rfl
  · exact .inr ⟨init, last, by rw [List.concat_eq_append]⟩

/-- **A6ι — classification of a `casesOn`-spine erasure.** Under a registered `casesOn`
head `con` (with `Γ.ctors con = none` by disjointness), the erasure of
`args.foldl Expr.app (.const con us)` is one of:

* **box cut at `k`** — the length-`k` prefix is `Erasable` and the remaining arguments
  are applied to `box`: `t = mkApps .box args'`; the whole spine is `Erasable` too
  (propagated with `Erasable.app`). `k = args.length` is the ordinary "the match is a
  proof" case (`args' = []`, `t = .box`); `k < args.length` is the derivation the
  shipping eraser never emits and that `IotaRelevant` excludes.
* **cases cut** — the rule fired at its pinned split (`dp` dropped arguments, the
  discriminant, one minor per constructor), with any surplus applied on top:
  `t = mkApps (.case (iid, np) discr' alts') rest'`. Note the cut is impossible below
  full arity, which is what `hsat` records.
* **block junk** — `¬ NoBlock t`, discharged by the caller's `NoBlock` premise. -/
theorem Erases.cases_spine_inv {env : VEnv} (henv : env.WF) {Us : List Name}
    {Γ : ErasureCtx} {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length Δ)
    {con : Name} {us : List Level} {iid : InductiveId} {np dp : Nat} {nfs : List Nat}
    (hc : Γ.casesOns con = some (iid, np))
    (hdp : Γ.casesDiscrPos con = some dp)
    (hnfs : Γ.ctorFields iid = some nfs)
    (hctors : Γ.ctors con = none) :
    ∀ (m : Nat) (args : List Expr), args.length = m → ∀ {ve : VExpr} {t : LBTerm},
      TrExprS env Us Δ (args.foldl Expr.app (.const con us)) ve →
      Erases env Us Γ Δ (args.foldl Expr.app (.const con us)) t →
      (∃ (k : Nat) (hk : k ≤ args.length) (vk : VExpr) (args' : List LBTerm)
          (hl : args.length - k = args'.length),
          TrExprS env Us Δ ((args.take k).foldl Expr.app (.const con us)) vk ∧
          Erasable env Us.length Δ.toCtx vk ∧
          Erasable env Us.length Δ.toCtx ve ∧
          (∀ i (h : i < args'.length),
             Erases env Us Γ Δ (args[k + i]'(by omega)) (args'[i]'h)) ∧
          t = LBTerm.mkApps .box args') ∨
      (∃ (discr' : LBTerm) (alts' : List (List BinderName × LBTerm)) (rest' : List LBTerm)
          (hsat : dp + 1 + nfs.length ≤ args.length)
          (hlen : alts'.length = nfs.length)
          (hrl : args.length - (dp + 1 + nfs.length) = rest'.length),
          Erases env Us Γ Δ (args[dp]'(by omega)) discr' ∧
          (∀ j (h : j < alts'.length), (alts'[j]'h).1.length = nfs[j]'(hlen ▸ h)) ∧
          (∀ j (h : j < alts'.length), Erases env Us Γ Δ (args[dp + 1 + j]'(by omega))
             (mkLambdas (alts'[j]'h).1 (alts'[j]'h).2)) ∧
          (∀ i (h : i < rest'.length),
             Erases env Us Γ Δ (args[dp + 1 + nfs.length + i]'(by omega)) (rest'[i]'h)) ∧
          t = LBTerm.mkApps (.case (iid, np) discr' alts') rest') ∨
      ¬ NoBlock t := by
  have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro args hm ve t htr her
    rcases list_nil_or_snoc args with rfl | ⟨init, last, rfl⟩
    · -- base: args = []; only `const_inv_full`'s five shapes are available
      simp only [List.foldl] at htr her
      rcases her.const_inv_full with ⟨ve', htr', her', rfl⟩ | ⟨kn, _, _, hcs, rfl⟩
        | ⟨iid2, cidx2, hc2, rfl⟩ | ⟨defs, fidx, _, _, hcs, rfl⟩ | ⟨x, _, _, hcs, rfl⟩
      · refine .inl ⟨0, by simp, ve', [], by simp, htr', her', ?_, by simp, by simp⟩
        exact her'.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htr' htr)
      · rw [hc] at hcs; exact absurd hcs (by simp)
      · rw [hctors] at hc2; exact absurd hc2 (by simp)
      · -- `const_fix` at a *registered `casesOn`* head: refuted by the leaf's own
        -- `Γ.casesOns = none` witness.
        rw [hc] at hcs; exact absurd hcs (by simp)
      · -- `fixvar` at a *registered `casesOn`* head: same witness, same refutation.
        rw [hc] at hcs; exact absurd hcs (by simp)
    · -- step: args = init ++ [last]
      have hspine : (init ++ [last]).foldl Expr.app (.const con us)
          = Expr.app (init.foldl Expr.app (.const con us)) last := by
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlenargs : (init ++ [last]).length = init.length + 1 := by simp
      rw [hspine] at htr her
      cases htr with
      | @app fve A B lastve _ _ _ hTf hTa htrf htrlast =>
        rcases her.app_inv_t with
          ⟨ve', htr'app, her'box, rfl⟩ |
          ⟨f', last', hf', hlast', rfl⟩ |
          ⟨cn2, us2, args2, iid2, cidx2, args'', hsrc, hc2, hlen2, rfl⟩ |
          ⟨con2, us2, pre2, discr2, minors2, iid2, np2, discr', alts', nfs2, hsrc,
            hcase2, hpre2, hnfs2, hd2, hlen2, hnlen2, harity2, halts2, rfl⟩
        · -- box on the whole current spine: cut at `k = args.length`
          have herve := her'box.defeq henv hΓ
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ)
              htr'app (.app hTf hTa htrf htrlast))
          refine .inl ⟨(init ++ [last]).length, Nat.le_refl _, _, [], by simp, ?_,
            herve, herve, by simp, by simp⟩
          rw [List.take_length, hspine]
          exact .app hTf hTa htrf htrlast
        · -- structural application: recurse on the init spine
          have hlt : init.length < m := by rw [← hm, hlenargs]; omega
          rcases ih init.length hlt init rfl htrf hf' with
            ⟨k, hk, vk, args'', hl, htrk, herk, herinit, hcorr, rfl⟩ |
            ⟨discr', alts', rest', hsat, hlen', hrl, hd, harity, halts, hrest, rfl⟩ | hnb
          · -- box cut for init → same cut for the whole spine (one more argument)
            refine .inl ⟨k, by simp; omega, vk, args'' ++ [last'], by simp; omega, ?_,
              herk, herinit.app henv hΓ hTf hTa, ?_, by rw [LBTerm.mkApps_concat]⟩
            · rwa [List.take_append_of_le_length hk]
            · intro i hi
              simp only [List.length_append, List.length_cons, List.length_nil] at hi
              by_cases hii : i < args''.length
              · rw [List.getElem_append_left (show k + i < init.length by omega),
                  List.getElem_append_left hii]
                exact hcorr i hii
              · have hieq : i = args''.length := by omega
                subst hieq
                have hki : k + args''.length = init.length := by omega
                simp only [hki, List.getElem_append_right, Nat.le_refl, Nat.sub_self,
                  List.getElem_cons_zero]
                simpa using hlast'
          · -- cases cut for init → same cut, one more surplus argument
            refine .inr (.inl ⟨discr', alts', rest' ++ [last'], by simp; omega, hlen',
              by simp; omega, ?_, harity, ?_, ?_, by rw [LBTerm.mkApps_concat]⟩)
            · rw [List.getElem_append_left (show dp < init.length by omega)]
              exact hd
            · intro j hj
              rw [List.getElem_append_left (show dp + 1 + j < init.length by omega)]
              exact halts j hj
            · intro i hi
              simp only [List.length_append, List.length_cons, List.length_nil] at hi
              by_cases hii : i < rest'.length
              · rw [List.getElem_append_left
                  (show dp + 1 + nfs.length + i < init.length by omega),
                  List.getElem_append_left hii]
                exact hrest i hii
              · have hieq : i = rest'.length := by omega
                subst hieq
                have hki : dp + 1 + nfs.length + rest'.length = init.length := by omega
                simp only [hki, List.getElem_append_right, Nat.le_refl, Nat.sub_self,
                  List.getElem_cons_zero]
                simpa using hlast'
          · exact .inr (.inr (fun hnbt => hnb hnbt.1))
        · -- block ctor rule on a `casesOn` head: contradicts ctors-disjointness
          exfalso
          have hfn : (Expr.app (init.foldl Expr.app (.const con us)) last).getAppFn
              = Expr.const con us := by
            rw [← hspine]; rw [expr_getAppFn_foldl]; rfl
          have hfn2 : (Expr.app (init.foldl Expr.app (.const con us)) last).getAppFn
              = Expr.const cn2 us2 := by
            rw [hsrc]; rw [expr_getAppFn_foldl]; rfl
          rw [hfn] at hfn2; injection hfn2 with hcncon
          rw [← hcncon, hctors] at hc2; exact absurd hc2 (by simp)
        · -- the rule fires on the whole current spine: exact-arity cases cut
          have hsrc' : (init ++ [last]).foldl Expr.app (.const con us)
              = (pre2 ++ discr2 :: minors2).foldl Expr.app (.const con2 us2) := by
            rw [hspine, hsrc, List.foldl_append]
          obtain ⟨rfl, rfl, hargeq⟩ := foldl_app_const_inj hsrc'
          obtain ⟨rfl, rfl⟩ : iid2 = iid ∧ np2 = np := by
            rw [hc] at hcase2; simpa using hcase2.symm
          obtain rfl : pre2.length = dp := by rw [hdp] at hpre2; simpa using hpre2.symm
          obtain rfl : nfs2 = nfs := by rw [hnfs] at hnfs2; simpa using hnfs2.symm
          have hmin : minors2.length = nfs2.length := by omega
          rw [hargeq]
          refine .inr (.inl ⟨discr', alts', [], by simp; omega, hnlen2, by simp; omega,
            ?_, harity2, ?_, by simp, by simp⟩)
          · simp only [List.getElem_append_right, Nat.le_refl, Nat.sub_self,
              List.getElem_cons_zero]
            exact hd2
          · intro j hj
            have hidx : pre2.length + 1 + j - pre2.length = j + 1 := by omega
            simp only [List.getElem_append_right
                (show pre2.length ≤ pre2.length + 1 + j by omega), hidx,
              List.getElem_cons_succ]
            exact halts2 j (by omega)

/-- **The ι redex's erasure, at exact arity.** With the source-side split pinned
(`pre.length = dp`, `minors.length = nfs.length`) and prefix-relevance assumed
(`hrel`), an ι redex erases either to `.box` — the whole match is irrelevant — or to a
`.case` whose split coincides, argument for argument, with the source split.

`hrel` is the specialisation of `IotaRelevant.partialCases` the ι simulation supplies:
it rules out the `Erases` derivations that box a *proper* prefix of the redex, which the
shipping eraser never emits (it boxes the whole application or none of it) but the
relation permits, and under which the target `.case` is stuck. Without it the box cut
could land at `k < args.length` and the reduct would carry unevaluated arguments no IH
covers. -/
theorem Erases.iota_redex_inv {env : VEnv} (henv : env.WF) {Us : List Name}
    {Γ : ErasureCtx} {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length Δ)
    {con : Name} {us : List Level} {iid : InductiveId} {np : Nat} {nfs : List Nat}
    {pre minors : List Expr} {discr : Expr}
    (hc : Γ.casesOns con = some (iid, np))
    (hdp : Γ.casesDiscrPos con = some pre.length)
    (hnfs : Γ.ctorFields iid = some nfs)
    (hctors : Γ.ctors con = none)
    (hmin : minors.length = nfs.length)
    {ve : VExpr} {t : LBTerm}
    (hrel : ∀ k, k < pre.length + 1 + nfs.length → ∀ {vk : VExpr},
        TrExprS env Us Δ (((pre ++ discr :: minors).take k).foldl Expr.app (.const con us)) vk →
        ¬ Erasable env Us.length Δ.toCtx vk)
    (htr : TrExprS env Us Δ
      ((discr :: minors).foldl Expr.app (pre.foldl Expr.app (.const con us))) ve)
    (her : Erases env Us Γ Δ
      ((discr :: minors).foldl Expr.app (pre.foldl Expr.app (.const con us))) t)
    (hnb : NoBlock t) :
    (Erasable env Us.length Δ.toCtx ve ∧ t = .box) ∨
    (∃ (discr' : LBTerm) (alts' : List (List BinderName × LBTerm))
        (hlen : alts'.length = nfs.length),
      t = .case (iid, np) discr' alts' ∧
      Erases env Us Γ Δ discr discr' ∧
      (∀ j (h : j < alts'.length), (alts'[j]'h).1.length = nfs[j]'(hlen ▸ h)) ∧
      (∀ j (h : j < alts'.length), Erases env Us Γ Δ (minors[j]'(by omega))
         (mkLambdas (alts'[j]'h).1 (alts'[j]'h).2))) := by
  have hspine : (discr :: minors).foldl Expr.app (pre.foldl Expr.app (.const con us))
      = (pre ++ discr :: minors).foldl Expr.app (.const con us) := by
    rw [List.foldl_append]
  rw [hspine] at htr her
  have hlenargs : (pre ++ discr :: minors).length = pre.length + 1 + nfs.length := by
    simp only [List.length_append, List.length_cons]; omega
  rcases Erases.cases_spine_inv henv hΔ hc hdp hnfs hctors
      (pre ++ discr :: minors).length (pre ++ discr :: minors) rfl htr her with
    ⟨k, hk, vk, args', hl, htrk, herk, herve, hcorr, rfl⟩ |
    ⟨discr', alts', rest', hsat, hlen, hrl, hd, harity, halts, hrest, rfl⟩ | hnbt
  · -- box cut: prefix-relevance forces it to the full length, so `args' = []`
    have hkeq : k = (pre ++ discr :: minors).length := by
      by_contra hne
      exact hrel k (by omega) htrk herk
    subst hkeq
    obtain rfl : args' = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact .inl ⟨herve, by simp⟩
  · -- cases cut: `hsat` is an equality, so there is no surplus
    obtain rfl : rest' = [] := List.eq_nil_of_length_eq_zero (by omega)
    refine .inr ⟨discr', alts', hlen, by simp, ?_, harity, ?_⟩
    · simpa only [List.getElem_append_right, Nat.le_refl, Nat.sub_self,
        List.getElem_cons_zero] using hd
    · intro j hj
      have hidx : pre.length + 1 + j - pre.length = j + 1 := by omega
      simpa only [List.getElem_append_right
          (show pre.length ≤ pre.length + 1 + j by omega), hidx,
        List.getElem_cons_succ] using halts j hj
  · exact absurd hnb hnbt

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
  /-- A **literal** evaluates by unfolding to its constructor form (see
      `SEvalβζδ.lit`). -/
  | lit {l : Literal} {r : Expr} :
      SEvalDataC Γ E l.toConstructor r → SEvalDataC Γ E (.lit l) r

/-- Embedding into the full (β+ζ+δ+ctor) `SEvalData`. -/
theorem SEvalDataC.toSEvalData {Γ : ErasureCtx} {E : SEnv} {e v : Expr}
    (h : SEvalDataC Γ E e v) : SEvalData Γ E e v := by
  induction h with
  | lam n ty b bi => exact .lam n ty b bi
  | beta _ _ _ ihf iha ihb => exact .beta ihf iha ihb
  | delta hu _ ih => exact .delta hu ih
  | ctor_val hc har hsat hl _ ihargs => exact .ctor_val hc har hsat hl (fun i h => ihargs i h)
  | lit _ ih => exact .lit ih

/-- **Erasure correctness — forward simulation, β + δ + saturated constructors, at
MetaRocq's non-block `appliedFlags`.**

If the source `e` translates to `ve`, erases to an **applied-form** (`NoBlock`) target
`t`, and evaluates to `v` under `SEvalDataC` (β/δ + saturated constructor values),
then `t` evaluates (`WcbvEval E appliedFlags`) to some `t'` that erases `v`, with `t'`
applied form and `v` translating to some `vve`.

Threads `SEnvConsistent` (source↔`VEnv` δ link for the `box` subject-reduction cases),
`ErasesEnvDeltaData` (target δ link + applied-form bodies), `ErasesEnvCtor` (arity
agreement), `hcc` (`ctors`/`casesOns` disjointness) and — since the recursion wall's
slice W2 — `RecEnvConsistent`, which replaces the retired `NoFixEnv E` and the `NoFix t`/
`NoFix t'` slots. The statement therefore holds of **recursive** environments; a
recursive head in the β case unfolds through `erases_lam_head_step` (one source β-step ↔
the head's `fix_guarded` stack + one `beta`), and a recursive constant in the δ case is a
value on both sides (`fix_atom`). -/
theorem erases_correct_data {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {Γ : ErasureCtx} {Esrc : SEnv} {E : GlobalDeclarations}
    (hcon : SEnvConsistent env Us Esrc)
    (hdelta : ErasesEnvDeltaData env Us Γ Esrc E)
    (hctorenv : ErasesEnvCtor Γ E)
    (hcc : ∀ {cn : Name} {iid : InductiveId} {cidx : Nat},
             Γ.ctors cn = some (iid, cidx) → Γ.casesOns cn = none)
    (hrec : RecEnvConsistent env Us Γ Esrc E)
    (hnfv : Γ.fixvars = fun _ => none)
    {e v : Expr} (hev : SEvalDataC Γ Esrc e v) :
    ∀ {ve : VExpr} {t : LBTerm},
      TrExprS env Us Δ e ve → Erases env Us Γ Δ e t → NoBlock t →
      ∃ t' vve, WcbvEval E appliedFlags t t' ∧ TrExprS env Us Δ v vve ∧
        Erases env Us Γ Δ v t' ∧ NoBlock t' := by
  have hnf : ∀ {n : Name} {body : Expr}, Esrc n = some body →
      Γ.ctors n = none ∧ Γ.casesOns n = none :=
    fun h => ⟨(hdelta (Δ := Δ) h).1, (hdelta (Δ := Δ) h).2.1⟩
  induction hev with
  | lam n ty b bi =>
      intro ve t htr her hnb
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      rcases Erases.lam_inv her with ⟨veb, htrb, herbox, rfl⟩ | ⟨_, _, hty, hb, rfl⟩
        | ⟨defs, idx, rfl, herfix⟩
      · exact ⟨.box, ve, .box, htr, .box htr
          (herbox.defeq henv hΓ
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)), trivial⟩
      · exact ⟨_, ve, .lam _ _, htr, .lam hty hb, hnb⟩
      · -- A recursive λ-value: the target block is already a value (`fix_atom`).
        exact ⟨_, ve, .fix_atom _ _, htr, herfix, hnb⟩
  | @beta f a n ty b bi av r hf ha hbody ihf iha ihbody =>
      intro ve t htr her hnb
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      rcases Erases.app_inv her with
        ⟨veb, htrb, herbox, rfl⟩ | ⟨f't, a't, hf', ha', rfl⟩ | ⟨cn, us, args, hspine, hmem⟩
      · obtain ⟨vve, htrr, hdef⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.beta hf.toSEvalData.toβζδ ha.toSEvalData.toβζδ hbody.toSEvalData.toβζδ)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hdef), trivial⟩
      · cases htr with
        | @app f' A B a'' _Δ _f _a hTf hTa htrf htra =>
          obtain ⟨ftv, fvv, hEf, htrlam, herlam, hnbftv⟩ := ihf htrf hf' hnb.1
          obtain ⟨atv, avv, hEa, htrav, herav, hnbatv⟩ := iha htra ha' hnb.2
          rcases erases_lam_head_step (P := NoBlock) rfl
              (fun hch hP => hch.noBlock hP) hEf hEa herlam hnbftv with
            ⟨velam, htrvelam, herlamE, hEbox⟩ | ⟨tyE, b', htrtyE, hb', hnbb', hEstep⟩
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
            exact ⟨.box, vve, hEbox, htrr,
              .box htrr (herapp.defeq henv hΓ hdef), trivial⟩
          · obtain ⟨fvv0, htrlam0, hfdef⟩ := SEvalβζδ_defeq henv hΔ hcon htrf hf.toSEvalData.toβζδ
            cases htrlam0 with
            | @lam ty' _Δ _ty _body body' _name _bi hty' htrty htrb =>
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
                noBlock_subst1 (by simpa [NoBlock] using hnbb') hnbatv
              obtain ⟨t', vve, hEr, htrr, herr, hnbt'⟩ := ihbody
                (TrExprS.inst henv.ordered havT htrb htrav)
                (erases_beta_struct henv.ordered htrav havTE hb' herav) hnbsub
              exact ⟨t', vve, hEstep hEr, htrr, herr, hnbt'⟩
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
      intro ve t htr her hnb
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      obtain ⟨bve, htrbody, hbdef⟩ := hcon hunf htr
      obtain ⟨hnoctor, _, body', hlook, herbody, hnbbody⟩ := hdelta hunf
      rcases Erases.const_inv her with ⟨veb, htrb, herbox, rfl⟩
        | ⟨kn, hkn, rfl⟩ | ⟨iid, cidx, hctor, rfl⟩ | ⟨defs, fidx, hrecn, rfl⟩
        | ⟨x, hfx, rfl⟩
      · obtain ⟨vve, htrr, hrdef⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.delta hunf hbodyev.toSEvalData.toβζδ)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hrdef), trivial⟩
      · obtain ⟨t', vve, hEbody, htrr, herr, hnbt'⟩ :=
          ihbody htrbody herbody hnbbody
        subst hkn
        exact ⟨t', vve, .delta hlook hEbody, htrr, herr, hnbt'⟩
      · rw [hnoctor] at hctor; exact absurd hctor (by simp)
      · -- `const_fix`: the constant stands for its own block. `RecEnvConsistent` says
        -- the source body it unfolds to erases to that same block, so the IH runs on
        -- the body against the block and delivers the target step (`fix_atom`, if the
        -- body is a λ-value) itself — no unfolding on either side.
        obtain ⟨_, _, _, body₀, hunf₀, her₀⟩ := hrec.reg hrecn
        rw [hunf] at hunf₀
        obtain rfl : body₀ = body := by simpa using hunf₀.symm
        exact ihbody htrbody her₀ hnb
      · -- `fixvar`: `hnfv` says `Γ` installs no fixvar map, so an in-block sibling
        -- reference cannot occur at a top-level evaluation.
        rw [hnfv] at hfx; exact absurd hfx (by simp)
  | @ctor_val cn us iid cidx ar args vs hcctors har hsat hl hargs ihargs =>
      intro ve t htr her hnb
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
          obtain ⟨w, _, hEa, _, _, _⟩ :=
            ihargs j hj htrsa (hsaj ▸ hera) (noBlock_mkApps_inv hnb a' ha')
          exact ⟨w, hEa⟩
        refine ⟨.box, vve, mkApps_headBox_eval WcbvEval.box heval, htrr,
          .box htrr (herve.defeq henv hΓ hdef), trivial⟩
      · -- headcut: t = mkApps (.construct iid cidx []) args'; A5 accumulates the args
        -- each source arg evaluates via its IH; collect (value, erasure, NoBlock).
        have hpt : ∀ i, i < args.length →
            ∃ w, ∃ (hiA : i < args'.length) (hiV : i < vs.length),
              WcbvEval E appliedFlags (args'[i]'hiA) w ∧
              Erases env Us Γ Δ (vs[i]'hiV) w ∧ NoBlock w := by
          intro i h
          have hiA : i < args'.length := hlen' ▸ h
          have hiV : i < vs.length := hl ▸ h
          obtain ⟨sve, htrsa⟩ := (trExprS_appSpine_inv args (.const cn us) ve htr).2 i h
          have hnba' : NoBlock (args'[i]'hiA) := noBlock_mkApps_inv hnb _ (List.getElem_mem _)
          obtain ⟨w, vve, hEa, htrvi, hervi, hnbw⟩ :=
            ihargs i h htrsa (hcorr i hiA) hnba'
          exact ⟨w, hiA, hiV, hEa, hervi, hnbw⟩
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
          obtain ⟨_, _, hE, _, _⟩ := hws i (hlaw ▸ hi)
          exact hE
        have hTeval := construct_app_spine harE args' ws (.construct iid cidx []) [] hbase hle hlaw hpe
        rw [← mkApps_eq_foldl, List.nil_append] at hTeval
        obtain ⟨vve, htrr, _⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.ctor_val hl (fun i h => (hargs i h).toSEvalData.toβζδ))
        have hVerase : Erases env Us Γ Δ (vs.foldl Expr.app (.const cn us))
            (LBTerm.mkApps (.construct iid cidx []) ws) := by
          refine erases_app_spine (.ctor_head cn us iid cidx hcctors) vs ws (by omega) ?_
          intro i hi
          obtain ⟨_, _, _, hEr, _⟩ := hws i (by omega)
          exact hEr
        have hVnb : NoBlock (LBTerm.mkApps (.construct iid cidx []) ws) := by
          refine noBlock_mkApps_construct (fun w hw => ?_)
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
          obtain ⟨_, _, _, _, hnbw⟩ := hws j hj
          exact hnbw
        exact ⟨_, vve, hTeval, htrr, hVerase, hVnb⟩
      · exact absurd hnb hnbt
  | @lit l r hev ih =>
      intro ve t htr her hnb
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      obtain ⟨hcl, htrC⟩ := TrExprS.lit_inv' htr
      rcases Erases.lit_inv her with ⟨veb, htrb, herbox, rfl⟩ | ⟨_, herC⟩
      · obtain ⟨vve, htrr, hdef⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.lit hev.toSEvalData.toβζδ)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hdef), trivial⟩
      · -- source and target both step to the unfolding: the IH *is* the goal
        exact ih htrC herC hnb

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
  | lit hcl _ ih => cases htyped with | lit _ h => exact .lit hcl (ih hΔ h)
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
  | fixvar nm us x hfx hctor hcases hfresh =>
      -- A context defeq moves neither source nor target; `VLCtx.IsDefEq.fvars` says it
      -- moves no fvar either, so the freshness premise re-applies at `Δ₂`.
      exact .fixvar nm us x hfx hctor hcases (hΔ.fvars ▸ hfresh)
  | const_fix nm us hrec hctor hcases hshift hsubst htobv =>
      exact .const_fix nm us hrec hctor hcases hshift hsubst htobv
  | @fix Δc idx nm tty tb tbi nms srcs defs hidx hnlen hslen hsrc hreg hrarg
      hlift hinst habsl hshift hsubst htobv hbodies _ihb =>
      -- Source/target unchanged by the context defeq; the fix bodies are context-uniform
      -- (`∀ Δf`), so the rule re-applies at the new conclusion context `Δ₂`.
      exact .fix idx hidx hnlen hslen hsrc hreg hrarg hlift hinst habsl hshift hsubst htobv
        hbodies

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
    (hrec : RecEnvConsistent env Us Γ Esrc E)
    (hnfv : Γ.fixvars = fun _ => none)
    {e v : Expr} (hev : SEvalData Γ Esrc e v) :
    ∀ {ve : VExpr} {t : LBTerm},
      TrExprS env Us Δ e ve → Erases env Us Γ Δ e t → NoBlock t →
      ∃ t' vve, WcbvEval E appliedFlags t t' ∧ TrExprS env Us Δ v vve ∧
        Erases env Us Γ Δ v t' ∧ NoBlock t' := by
  have hnf : ∀ {n : Name} {body : Expr}, Esrc n = some body →
      Γ.ctors n = none ∧ Γ.casesOns n = none :=
    fun h => ⟨(hdelta (Δ := Δ) h).1, (hdelta (Δ := Δ) h).2.1⟩
  induction hev with
  | lam n ty b bi =>
      intro ve t htr her hnb
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      rcases Erases.lam_inv her with ⟨veb, htrb, herbox, rfl⟩ | ⟨_, _, hty, hb, rfl⟩
        | ⟨defs, idx, rfl, herfix⟩
      · exact ⟨.box, ve, .box, htr, .box htr
          (herbox.defeq henv hΓ
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)), trivial⟩
      · exact ⟨_, ve, .lam _ _, htr, .lam hty hb, hnb⟩
      · -- A recursive λ-value: the target block is already a value (`fix_atom`).
        exact ⟨_, ve, .fix_atom _ _, htr, herfix, hnb⟩
  | @beta f a n ty b bi av r hf ha hbody ihf iha ihbody =>
      intro ve t htr her hnb
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      rcases Erases.app_inv her with
        ⟨veb, htrb, herbox, rfl⟩ | ⟨f't, a't, hf', ha', rfl⟩ | ⟨cn, us, args, hspine, hmem⟩
      · obtain ⟨vve, htrr, hdef⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.beta hf.toβζδ ha.toβζδ hbody.toβζδ)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hdef), trivial⟩
      · cases htr with
        | @app f' A B a'' _Δ _f _a hTf hTa htrf htra =>
          obtain ⟨ftv, fvv, hEf, htrlam, herlam, hnbftv⟩ := ihf htrf hf' hnb.1
          obtain ⟨atv, avv, hEa, htrav, herav, hnbatv⟩ := iha htra ha' hnb.2
          rcases erases_lam_head_step (P := NoBlock) rfl
              (fun hch hP => hch.noBlock hP) hEf hEa herlam hnbftv with
            ⟨velam, htrvelam, herlamE, hEbox⟩ | ⟨tyE, b', htrtyE, hb', hnbb', hEstep⟩
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
            exact ⟨.box, vve, hEbox, htrr,
              .box htrr (herapp.defeq henv hΓ hdef), trivial⟩
          · obtain ⟨fvv0, htrlam0, hfdef⟩ := SEvalβζδ_defeq henv hΔ hcon htrf hf.toβζδ
            cases htrlam0 with
            | @lam ty' _Δ _ty _body body' _name _bi hty' htrty htrb =>
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
                noBlock_subst1 (by simpa [NoBlock] using hnbb') hnbatv
              obtain ⟨t', vve, hEr, htrr, herr, hnbt'⟩ := ihbody
                (TrExprS.inst henv.ordered havT htrb htrav)
                (erases_beta_struct henv.ordered htrav havTE hb' herav) hnbsub
              exact ⟨t', vve, hEstep hEr, htrr, herr, hnbt'⟩
      · rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
        · exact absurd hspine (by simp)
        · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons,
            List.foldl_nil] at hspine
          injection hspine with hf_eq _
          exact absurd ⟨n, ty, b, bi, rfl⟩
            (SEvalData_const_spine_lam_elim hnf hf hf_eq hmem)
  | @zeta n ty v b nd vv r hval_ev hbody_ev ihval ihbody =>
      intro ve t htr her hnb
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      rcases Erases.letE_inv her with ⟨veb, htrb, herbox, rfl⟩
        | ⟨ty'ₑ, val'ₑ, v', b', hty_e, hval_e, hv_er, hb_er, rfl⟩
      · obtain ⟨vve, htrr, hdef⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.zeta hval_ev.toβζδ hbody_ev.toβζδ)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hdef), trivial⟩
      · cases htr with
        | @letE val'_T ty'_T _ _ _ _ _ _ _ hValT htrty_T htrval_T htrb_T =>
          obtain ⟨vtv, vvve, hEv, htr_vv, her_vv, hnb_vtv⟩ :=
            ihval hval_e hv_er hnb.1
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
          obtain ⟨t', vve, hEr', htrr, herr, hnbt'⟩ :=
            ihbody htr_sub hb_reduct_er hnb_reduct
          exact ⟨t', vve, .zeta hEv hEr', htrr, herr, hnbt'⟩
  | @delta n us body r hunf hbodyev ihbody =>
      intro ve t htr her hnb
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      obtain ⟨bve, htrbody, hbdef⟩ := hcon hunf htr
      obtain ⟨hnoctor, _, body', hlook, herbody, hnbbody⟩ := hdelta hunf
      rcases Erases.const_inv her with ⟨veb, htrb, herbox, rfl⟩
        | ⟨kn, hkn, rfl⟩ | ⟨iid, cidx, hctor, rfl⟩ | ⟨defs, fidx, hrecn, rfl⟩
        | ⟨x, hfx, rfl⟩
      · obtain ⟨vve, htrr, hrdef⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.delta hunf hbodyev.toβζδ)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hrdef), trivial⟩
      · obtain ⟨t', vve, hEbody, htrr, herr, hnbt'⟩ :=
          ihbody htrbody herbody hnbbody
        subst hkn
        exact ⟨t', vve, .delta hlook hEbody, htrr, herr, hnbt'⟩
      · rw [hnoctor] at hctor; exact absurd hctor (by simp)
      · -- `const_fix`: see `erases_correct_data`'s δ case — `RecEnvConsistent` turns
        -- the block back into the source body's erasure and the IH does the rest.
        obtain ⟨_, _, _, body₀, hunf₀, her₀⟩ := hrec.reg hrecn
        rw [hunf] at hunf₀
        obtain rfl : body₀ = body := by simpa using hunf₀.symm
        exact ihbody htrbody her₀ hnb
      · -- `fixvar`: `hnfv` says `Γ` installs no fixvar map, so an in-block sibling
        -- reference cannot occur at a top-level evaluation.
        rw [hnfv] at hfx; exact absurd hfx (by simp)
  | @ctor_val cn us iid cidx ar args vs hcctors har hsat hl hargs ihargs =>
      intro ve t htr her hnb
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
          obtain ⟨w, _, hEa, _, _, _⟩ :=
            ihargs j hj htrsa (hsaj ▸ hera) (noBlock_mkApps_inv hnb a' ha')
          exact ⟨w, hEa⟩
        refine ⟨.box, vve, mkApps_headBox_eval WcbvEval.box heval, htrr,
          .box htrr (herve.defeq henv hΓ hdef), trivial⟩
      · have hpt : ∀ i, i < args.length →
            ∃ w, ∃ (hiA : i < args'.length) (hiV : i < vs.length),
              WcbvEval E appliedFlags (args'[i]'hiA) w ∧
              Erases env Us Γ Δ (vs[i]'hiV) w ∧ NoBlock w := by
          intro i h
          have hiA : i < args'.length := hlen' ▸ h
          have hiV : i < vs.length := hl ▸ h
          obtain ⟨sve, htrsa⟩ := (trExprS_appSpine_inv args (.const cn us) ve htr).2 i h
          have hnba' : NoBlock (args'[i]'hiA) := noBlock_mkApps_inv hnb _ (List.getElem_mem _)
          obtain ⟨w, vve, hEa, htrvi, hervi, hnbw⟩ :=
            ihargs i h htrsa (hcorr i hiA) hnba'
          exact ⟨w, hiA, hiV, hEa, hervi, hnbw⟩
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
          obtain ⟨_, _, hE, _, _⟩ := hws i (hlaw ▸ hi)
          exact hE
        have hTeval := construct_app_spine harE args' ws (.construct iid cidx []) [] hbase hle hlaw hpe
        rw [← mkApps_eq_foldl, List.nil_append] at hTeval
        obtain ⟨vve, htrr, _⟩ :=
          SEvalβζδ_defeq henv hΔ hcon htr (.ctor_val hl (fun i h => (hargs i h).toβζδ))
        have hVerase : Erases env Us Γ Δ (vs.foldl Expr.app (.const cn us))
            (LBTerm.mkApps (.construct iid cidx []) ws) := by
          refine erases_app_spine (.ctor_head cn us iid cidx hcctors) vs ws (by omega) ?_
          intro i hi
          obtain ⟨_, _, _, hEr, _⟩ := hws i (by omega)
          exact hEr
        have hVnb : NoBlock (LBTerm.mkApps (.construct iid cidx []) ws) := by
          refine noBlock_mkApps_construct (fun w hw => ?_)
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
          obtain ⟨_, _, _, _, hnbw⟩ := hws j hj
          exact hnbw
        exact ⟨_, vve, hTeval, htrr, hVerase, hVnb⟩
      · exact absurd hnb hnbt
  | @lit l r hev ih =>
      intro ve t htr her hnb
      have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
      obtain ⟨hcl, htrC⟩ := TrExprS.lit_inv' htr
      rcases Erases.lit_inv her with ⟨veb, htrb, herbox, rfl⟩ | ⟨_, herC⟩
      · obtain ⟨vve, htrr, hdef⟩ := SEvalβζδ_defeq henv hΔ hcon htr (.lit hev.toβζδ)
        have herve : Erasable env Us.length Δ.toCtx ve := herbox.defeq henv hΓ
          (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrb htr)
        exact ⟨.box, vve, .box, htrr, .box htrr (herve.defeq henv hΓ hdef), trivial⟩
      · exact ih htrC herC hnb

/-! ## Non-vacuity guards for the literal fragment

The `lit` rules are only worth having if a literal really *runs*: on the source it must
reach a value, on the target the erased tower must be a `WcbvEval` value, and the two
must be linked by `Erases`. All three are exhibited below, at every `n`, over the
constructed `envNatLit`/`ΓnatLit` of `Erases.lean` and a target env `EnatLit` declaring
`Nat` exactly as `register_inductive` would (`npars = 0`, `nargs = 0`/`1` — verified
against the kernel).

Together these are the conclusion of `erases_correct_data` for a literal source, spelled
out concretely: `.lit (.natVal n)` evaluates to `srcNatTower n`, the target
`natLitTower n` evaluates to itself, `srcNatTower n` erases to `natLitTower n`, and the
result is in the simulable fragment (`NoBlock`, `NoFix`). No new target-side rule was
needed: `construct_atom`/`construct_app` already do it. -/

/-- The target environment for `Nat`: one mutual block, no parameters, constructors
`Nat.zero` (0 fields) and `Nat.succ` (1 field). -/
def EnatLit : GlobalDeclarations :=
  [(toKername ``Nat, .inductiveDecl
      { npars := 0
        bodies := [{ name := "Nat"
                     ctors := [⟨"Nat.zero", 0⟩, ⟨"Nat.succ", 1⟩]
                     projs := [] }] })]

theorem EnatLit_arity_zero : constructorArity EnatLit natLitInd 0 = some 0 := rfl
theorem EnatLit_arity_succ : constructorArity EnatLit natLitInd 1 = some 1 := rfl

/-- The `Γ`/target arity link the simulation threads, discharged for `Nat`. -/
theorem erasesEnvCtor_natLit : ErasesEnvCtor ΓnatLit EnatLit := by
  intro cn iid cidx ar hc har
  by_cases h0 : cn = ``Nat.zero
  · subst h0
    rw [ΓnatLit_zero] at hc; rw [ΓnatLit_arity_zero] at har
    simp only [Option.some.injEq, Prod.mk.injEq] at hc har
    obtain ⟨rfl, rfl⟩ := hc; subst har; exact EnatLit_arity_zero
  · by_cases h1 : cn = ``Nat.succ
    · subst h1
      rw [ΓnatLit_succ] at hc; rw [ΓnatLit_arity_succ] at har
      simp only [Option.some.injEq, Prod.mk.injEq] at hc har
      obtain ⟨rfl, rfl⟩ := hc; subst har; exact EnatLit_arity_succ
    · rw [ΓnatLit_ctors_other h0 h1] at hc; exact absurd hc (by simp)

/-- **Target side**: the peano tower is a `WcbvEval` value under `appliedFlags`, by
`construct_atom` at the base and `construct_app` at each `succ` — no new rule. -/
theorem wcbvEval_natLitTower : ∀ n : Nat,
    WcbvEval EnatLit appliedFlags (natLitTower n) (natLitTower n)
  | 0 => WcbvEval.construct_atom rfl EnatLit_arity_zero
  | n + 1 => by
      refine WcbvEval.construct_app (args := []) rfl ?_ EnatLit_arity_succ
        (by simp) (wcbvEval_natLitTower n)
      simpa using WcbvEval.construct_atom (Γ := EnatLit) (fl := appliedFlags) rfl
        EnatLit_arity_succ

theorem noBlock_natLitTower : ∀ n : Nat, NoBlock (natLitTower n)
  | 0 => trivial
  | n + 1 => ⟨trivial, noBlock_natLitTower n⟩

theorem noFix_natLitTower : ∀ n : Nat, NoFix (natLitTower n)
  | 0 => trivial
  | n + 1 => ⟨trivial, noFix_natLitTower n⟩

/-- The **source** value of a peano literal: the constructor tower
`Nat.succ (… (Nat.zero))`, in the same `.const`-headed application-spine encoding the
`ctor_val` rules use. `.lit (.natVal n)` is *not* itself a value — it unfolds. -/
def srcNatTower : Nat → Expr
  | 0 => .const ``Nat.zero []
  | n + 1 => .app (.const ``Nat.succ []) (srcNatTower n)

/-- **Source side**: a literal evaluates, by `lit` unfolding into `ctor_val` at each
step. The saturation bounds come from `ΓnatLit.ctorArities` (`0` and `1`). -/
theorem sevalData_natLit {E : SEnv} : ∀ n : Nat,
    SEvalData ΓnatLit E (.lit (.natVal n)) (srcNatTower n)
  | 0 => .lit (.ctor_val (args := []) (vs := []) ΓnatLit_zero ΓnatLit_arity_zero
      (Nat.le_refl 0) rfl (fun i hi => absurd hi (by simp)))
  | n + 1 => .lit (.ctor_val (args := [.lit (.natVal n)]) (vs := [srcNatTower n])
      ΓnatLit_succ ΓnatLit_arity_succ (Nat.le_refl 1) rfl
      (fun i hi => by
        obtain rfl : i = 0 := by simpa using hi
        exact sevalData_natLit n))

/-- **The link**: the source value erases to the target tower — so the simulation's
conclusion is inhabited at a literal source. -/
theorem erases_srcNatTower (Us : List Name) (Δ : VLCtx) : ∀ n : Nat,
    Erases envNatLit Us ΓnatLit Δ (srcNatTower n) (natLitTower n)
  | 0 => .ctor_head ``Nat.zero [] natLitInd 0 ΓnatLit_zero
  | n + 1 => .app (.ctor_head ``Nat.succ [] natLitInd 1 ΓnatLit_succ)
      (erases_srcNatTower Us Δ n)

/-- The whole literal instance of `erases_correct_data`'s conclusion, at `n = 2`: the
source literal evaluates to the tower, the erased term evaluates to the erased tower,
and the two are related by `Erases` in applied (`NoBlock`, `NoFix`) form. -/
example (Us : List Name) (Δ : VLCtx) {E : SEnv} :
    SEvalData ΓnatLit E (.lit (.natVal 2)) (srcNatTower 2) ∧
    Erases envNatLit Us ΓnatLit Δ (.lit (.natVal 2)) (natLitTower 2) ∧
    WcbvEval EnatLit appliedFlags (natLitTower 2) (natLitTower 2) ∧
    Erases envNatLit Us ΓnatLit Δ (srcNatTower 2) (natLitTower 2) ∧
    NoBlock (natLitTower 2) ∧ NoFix (natLitTower 2) :=
  ⟨sevalData_natLit 2, erases_natLit Us Δ 2, wcbvEval_natLitTower 2,
    erases_srcNatTower Us Δ 2, noBlock_natLitTower 2, noFix_natLitTower 2⟩

end LeanToLambdaBox
