import LeanToLambdaBox.Basic
import LeanToLambdaBox.ErasureContext
import LeanToLambdaBox.Semantics.Substitution
import LeanToLambdaBox.Erasability
import LeanToLambdaBox.FixMetatheory
import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Verify.Typing.Lemmas

/-!
# Typed erasure relation over real `Lean.Expr` (step A2.1)

This is the erasure relation grounded on lean4lean: `LeanToLambdaBox.Erases` relates
the **real** `Lean.Expr` to `LBTerm`, and its `box` rule carries a genuine irrelevance
witness phrased over lean4lean's `VExpr` typing (`TrExprS` + `Erasable`). (It replaced
an earlier hand-written-IR (`CExpr`) stub with a trivial box rule, now removed.)

Both languages are locally-nameless (`bvar`/`fvar`), so they line up
constructor-for-constructor; the typing premise on `box` lives over `VExpr`, so
the relation threads a lean4lean `VLCtx` (extended under binders exactly as
`TrExprS` does).

## Scope (documented, deliberate)

* **Projection-free.** `.proj`/`LBTerm.proj` are excluded. The original reason was
  that lean4lean's projection translation `TrProj` was a `sorry`, so including them
  would have made every downstream result rest on lean4lean sorries. **That reason
  expired at the `fee3ada` re-pin (2026-08-27):** `TrProj` now has a real definition —
  an ι-pattern membership in `env.pats` plus a `HasType` conjunct — and measures
  `[propext]`. A projection rule for `Erases` is therefore *writable*, which is the
  unlock the typeclass-method layer (6–10 `tProj` per VerifyBench program) has been
  waiting on. What still blocks it is downstream and ours: `Supported` has no `.proj`
  rule (`Bridge.lean`), and `TrProj.uniq` — the lemma an inversion would want — is one
  of the two remaining upstream `PROJ-TODO`s. Adding the rule is a design call, not a
  mechanical follow-on; until it is made, the fragment stays as documented here.
* **Constructors / `casesOn` / structural recursion ARE modelled** (aligning the
  relation with what `visitExpr` emits), via dedicated `ctor`/`cases`/`fix` rules
  producing `.construct`/`.case`/`.fix`. In real `Expr` these heads are applied
  `.const`s; the rules carry the inductive metadata via `Γ` (`ctors`/`casesOns`)
  rather than running environment queries. We use the **abstract** target form
  (constructor args inside `.construct`; alternatives as `(field-names, body)`),
  reusing the semantics' ι-rule (`Semantics/Eval.lean`); the wrapping of the
  implementation's literal output (`.construct iid k []` applied via `.app`; minor
  functions) into this abstract structure is anchored in Half B's `erase_refines_Erases`.
* `machine`-`Nat`/`Int` lowering and `@[extern]`/`@[csimp]` rewrites are out of
  scope (documented), as before.

This relation covers the projection-free fragment:
`box | lit | bvar | fvar | const | app | lam | letE | ctor | ctor_head | cases |
fixvar | const_fix | fix`.

## Trust boundary: inherited `sorryAx`

**Rewritten at the `fee3ada` re-pin, 2026-08-27.** This section used to say that
lean4lean's reusable `TrExprS` structural lemmas (`weakBV`, `inst`, `instN`, …) carry
`sorryAx` because they are monolithic inductions whose `proj` case calls a sorried
`TrProj`, and that every result here inherits it *even on projection-free terms*. Both
halves are now out of date:

* `TrProj` has a real definition, so it no longer taints the **type** of `TrExprS` —
  which was the actual mechanism, and a stronger one than "the structural lemmas call
  it": it meant merely *mentioning* `Erases` cost a `sorryAx`, proof or no proof.
* The structural lemmas themselves came back clean: `TrExprS.weakFV'`, `.weakBV`,
  `.mono`, `.instN`, `.weakFV`, `.inst` all measure
  `[propext, Classical.choice, Quot.sound]`. So `erases_shift`, `erases_subst`,
  `Erases.abstract`, `Erases.thin_vlet` and the rest of the transport family are
  **sorryAx-free**, and so is `visitExpr_refines_erases`.

What is still inherited, and where: the **unique-typing** cluster —
`Lean4Lean.TrExprS.uniq` (whose `proj` arm calls `TrProj.uniq`, still `PROJ-TODO`) and
`Lean4Lean.VEnv.IsDefEq.uniqU` (sorried through `IsDefEqU.weakN_iff` and the ι fork's
`pat` cases) — plus `VEnv.HasType.app_inv` and `Aligned.addInduct` on the ι side. That is
what the forward-simulation results (`erases_correct*`, the `SEval*` family) and hence the
capstones report. The posture is unchanged and intentional: lean4lean's job is to prove
the Lean kernel correct, ours to prove the transpilation pipeline correct **assuming**
that, and the `sorryAx` reported by `#print axioms` is exactly the boundary "modulo the
Lean kernel's correctness as formalized by lean4lean". What changed is that the boundary
is now much narrower, and located where the proofs actually use it rather than smeared
over every statement. Full measurement in `ColdStart.lean`'s inherited-boundary section
and in `scratch/final_audit.lean`'s header. See also memory `lean4lean-sorry-boundary`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ### `LBTerm.recData`: data-oriented recursor

A `Prop`-motive recursor for `LBTerm` that hands per-list membership IHs (rather than
raw nested-inductive motives), used by the `NoFix`/`NoBlock` de-Bruijn-preservation
lemmas. Lives here (rather than in `ErasesCorrectData`) so `NoFix`'s lemmas — needed
already in `ErasesCorrect` for the fix-source ripple — can share it. -/
@[elab_as_elim]
def LBTerm.recData
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

/-! ### The `shift`/`subst` list traversals in `List.map` form

`LBTerm.shiftArgs`/`shiftAlts`/`shiftDefs` (and their `subst` counterparts) are
hand-rolled traversals (the structural-recursion checker cannot see through `List.map`
for a nested inductive). These six lemmas expose them as maps, which is what every
`LBTerm.recData` induction below needs in its `hconstruct`/`hcase`/`hfix` arm. Stated
here (rather than after `mkLambdas`, where they used to live) because
`noFix_shift`/`noFix_subst` now have a `.case` arm; the two `Defs` variants moved up
from `Closed.lean` for the same reason, once `noBlock_shift`/`noBlock_subst` gained a
`.fix` arm (recursion wall, slice W0). -/

theorem LBTerm.shiftArgs_eq_map (d c : Nat) (l : List LBTerm) :
    LBTerm.shiftArgs d c l = l.map (LBTerm.shift d c) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [LBTerm.shiftArgs, List.map, ih]

theorem LBTerm.substArgs_eq_map (s : LBTerm) (d : Nat) (l : List LBTerm) :
    LBTerm.substArgs s d l = l.map (LBTerm.subst s d) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [LBTerm.substArgs, List.map, ih]

theorem LBTerm.shiftAlts_eq_map (d c : Nat) (l : List (List BinderName × LBTerm)) :
    LBTerm.shiftAlts d c l = l.map (fun a => (a.1, LBTerm.shift d (c + a.1.length) a.2)) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [LBTerm.shiftAlts, List.map, ih]

theorem LBTerm.substAlts_eq_map (s : LBTerm) (d : Nat) (l : List (List BinderName × LBTerm)) :
    LBTerm.substAlts s d l = l.map (fun a => (a.1, LBTerm.subst s (d + a.1.length) a.2)) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [LBTerm.substAlts, List.map, ih]

theorem LBTerm.shiftDefs_eq_map (d c : Nat) (l : List (@FixDef LBTerm)) :
    LBTerm.shiftDefs d c l = l.map (fun fd => { fd with body := LBTerm.shift d c fd.body }) := by
  induction l with
  | nil => rfl
  | cons fd rest ih => simp only [LBTerm.shiftDefs, List.map, ih]

theorem LBTerm.substDefs_eq_map (s : LBTerm) (d : Nat) (l : List (@FixDef LBTerm)) :
    LBTerm.substDefs s d l = l.map (fun fd => { fd with body := LBTerm.subst s d fd.body }) := by
  induction l with
  | nil => rfl
  | cons fd rest ih => simp only [LBTerm.substDefs, List.map, ih]

/-! ### `NoFix`: fix-free target terms

`NoFix t` holds when `t` contains no `.fix` node in relevant (spine) position.

**Status (recursion wall, slice W2).** `NoFix` is no longer a hypothesis of the forward
simulations — they accept `.fix` targets, and what replaces it is the registration-level
`RecEnvConsistent` (`ErasesCorrect`). The predicate and its shift/subst/mkApps kit stay:
they are still the right tool wherever a genuinely fix-free fragment is wanted
(`erases_correct_beta`, which has no environment at all, still carries `NoFix t`), and
the historical record of why it *was* load-bearing lives in `EnvErasureRec`.

The shipping `visitExpr` **never** emits `.fix` (only the environment-level `visitMutual`
does — P3), so every `visitExpr` output is `NoFix`. It *was* threaded through the
forward-simulation theorems purely to discharge the (vacuous, in that fragment) `.fix`
disjunct that `Erases.lam_inv` gains once `Erases.fix` is added: a `.lam`-source that
erases via the fix rule has target `.fix …`, and `NoFix (.fix …)` is `False`.

`.construct` is opaque (`True`): the data fragment's applied-form
constructor spines carry their arguments through `.app` (`mkApps (.construct … []) args`),
so `NoFix` reaches them via the `.app` recursion, not the (always-empty) `.construct`
node.

`.proj` is **not** opaque (projection round, slice P0). It used to be, and the reason
given above covered only `.construct`: `.proj` was unreachable, because `Erases` had no
projection rule and so never produced one. Once `Erases.proj` exists,
`NoFix (.proj p t) = True` hides an arbitrary `t` — a `.fix` under a projection would
satisfy `NoFix` and then take a `fix_guarded` step the simulation has no case for. The
change is the one ι Task 3 made to `.case`, one node simpler (a projection has exactly
one child and no alternative list, so no mutual helper is needed). It is a
*strengthening*, so every hypothesis-position consumer is unaffected; the cost is the
conclusion-position `hproj` arms of the `LBTerm.recData` inductions, which become
`exact ih …` instead of `trivial`.

`.case` is **not** opaque (ι Task 3): the ι forward simulation inverts a target
`.case (iid, np) discr' alts'` and must hand `NoFix discr'` to the discriminant IH and
`NoFix (alts'[cidx]).2` to the branch IH. With a `True` clause neither is obtainable, so
the ι case could not even be started. The per-alternative traversal is factored into the
mutual helper `NoFixAlts` (as `LBClosedAlts` does for `LBClosed`) because the nested-list
occurrence defeats the structural-recursion checker in `∀ a ∈ alts, NoFix a.2` form;
`NoFix_case`/`NoFixAlts_iff` below expose exactly that form. -/
mutual
def NoFix : LBTerm → Prop
  | .lambda _ b => NoFix b
  | .letIn _ v b => NoFix v ∧ NoFix b
  | .app f a => NoFix f ∧ NoFix a
  | .case _ d alts => NoFix d ∧ NoFixAlts alts
  | .fix _ _ => False
  | .box => True
  | .bvar _ => True
  | .fvar _ => True
  | .const _ => True
  | .construct _ _ _ => True
  | .proj _ e => NoFix e
  | .prim _ => True

/-- `NoFix` over `case` alternatives (each branch body is `NoFix`). -/
def NoFixAlts : List (List BinderName × LBTerm) → Prop
  | [] => True
  | (_, b) :: rest => NoFix b ∧ NoFixAlts rest
end

/-- `NoFixAlts` in the natural per-element form. -/
theorem NoFixAlts_iff (l : List (List BinderName × LBTerm)) :
    NoFixAlts l ↔ ∀ a ∈ l, NoFix a.2 := by
  induction l with
  | nil => simp [NoFixAlts]
  | cons a rest ih => obtain ⟨ns, b⟩ := a; simp [NoFixAlts, ih]

@[simp] theorem NoFix_box : NoFix .box := trivial
@[simp] theorem NoFix_bvar (i : Nat) : NoFix (.bvar i) := trivial
@[simp] theorem NoFix_fvar (x : FVarId) : NoFix (.fvar x) := trivial
@[simp] theorem NoFix_const (kn : Kername) : NoFix (.const kn) := trivial
@[simp] theorem NoFix_construct (iid : InductiveId) (c : Nat) (args : List LBTerm) :
    NoFix (.construct iid c args) := trivial
@[simp] theorem NoFix_fix (defs : List (@FixDef LBTerm)) (i : Nat) :
    NoFix (.fix defs i) ↔ False := Iff.rfl
@[simp] theorem NoFix_lambda (n : BinderName) (b : LBTerm) :
    NoFix (.lambda n b) ↔ NoFix b := Iff.rfl
@[simp] theorem NoFix_letIn (n : BinderName) (v b : LBTerm) :
    NoFix (.letIn n v b) ↔ NoFix v ∧ NoFix b := Iff.rfl
@[simp] theorem NoFix_app (f a : LBTerm) :
    NoFix (.app f a) ↔ NoFix f ∧ NoFix a := Iff.rfl
@[simp] theorem NoFix_case (info : InductiveId × Nat) (d : LBTerm)
    (alts : List (List BinderName × LBTerm)) :
    NoFix (.case info d alts) ↔ NoFix d ∧ ∀ a ∈ alts, NoFix a.2 := by
  show NoFix d ∧ NoFixAlts alts ↔ _
  rw [NoFixAlts_iff]
@[simp] theorem NoFix_proj (p : ProjectionInfo) (e : LBTerm) :
    NoFix (.proj p e) ↔ NoFix e := Iff.rfl
@[simp] theorem NoFix_prim (p : PrimVal) : NoFix (.prim p) := trivial

/-- `NoFix` is preserved by de Bruijn shifting. -/
theorem noFix_shift {s : LBTerm} (hs : NoFix s) (d c : Nat) :
    NoFix (LBTerm.shift d c s) := by
  induction s using LBTerm.recData generalizing c with
  | hbvar i => simp only [LBTerm.shift]; split <;> trivial
  | hlam n b ih => exact ih hs (c + 1)
  | hletIn n v b ihv ihb => exact ⟨ihv hs.1 c, ihb hs.2 (c + 1)⟩
  | happ f a ihf iha => exact ⟨ihf hs.1 c, iha hs.2 c⟩
  | hcase info discr alts ihd iha =>
      rw [NoFix_case] at hs
      simp only [LBTerm.shift, NoFix_case, LBTerm.shiftAlts_eq_map]
      refine ⟨ihd hs.1 c, fun a ha => ?_⟩
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact iha b hb (hs.2 b hb) _
  | hfix defs i _ => exact absurd hs (by simp [NoFix])
  | hproj p e ih => exact ih hs c
  | _ => trivial

/-- `NoFix` is preserved by substitution (the substitutee `s` must be `NoFix` too). -/
theorem noFix_subst {t : LBTerm} (ht : NoFix t) {s : LBTerm} (hs : NoFix s)
    (d : Nat) : NoFix (LBTerm.subst s d t) := by
  induction t using LBTerm.recData generalizing d with
  | hbvar i =>
      simp only [LBTerm.subst]
      split
      · trivial
      · split
        · exact noFix_shift hs d 0
        · trivial
  | hlam n b ih => exact ih ht (d + 1)
  | hletIn n v b ihv ihb => exact ⟨ihv ht.1 d, ihb ht.2 (d + 1)⟩
  | happ f a ihf iha => exact ⟨ihf ht.1 d, iha ht.2 d⟩
  | hcase info discr alts ihd iha =>
      rw [NoFix_case] at ht
      simp only [LBTerm.subst, NoFix_case, LBTerm.substAlts_eq_map]
      refine ⟨ihd ht.1 d, fun a ha => ?_⟩
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact iha b hb (ht.2 b hb) _
  | hfix defs i _ => exact absurd ht (by simp [NoFix])
  | hproj p e ih => exact ih ht d
  | _ => trivial

theorem noFix_subst1 {t s : LBTerm} (ht : NoFix t) (hs : NoFix s) :
    NoFix (LBTerm.subst1 s t) := noFix_subst ht hs 0

/-- A `NoFix`-headed application spine with `NoFix` arguments is `NoFix`. -/
theorem noFix_mkApps {hd : LBTerm} (hhd : NoFix hd) {args : List LBTerm}
    (h : ∀ a ∈ args, NoFix a) : NoFix (LBTerm.mkApps hd args) := by
  induction args generalizing hd with
  | nil => exact hhd
  | cons a as ih =>
      rw [LBTerm.mkApps]
      exact ih ⟨hhd, h a (List.mem_cons_self ..)⟩ (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- The head of a `NoFix` application spine is `NoFix`. -/
theorem noFix_mkApps_head {hd : LBTerm} {args : List LBTerm}
    (h : NoFix (LBTerm.mkApps hd args)) : NoFix hd := by
  induction args generalizing hd with
  | nil => exact h
  | cons a as ih => rw [LBTerm.mkApps] at h; exact (ih h).1

/-- Each argument of a `NoFix` application spine is `NoFix`. -/
theorem noFix_mkApps_inv {hd : LBTerm} {args : List LBTerm}
    (h : NoFix (LBTerm.mkApps hd args)) : ∀ a ∈ args, NoFix a := by
  induction args generalizing hd with
  | nil => intro a ha; exact absurd ha (by simp)
  | cons a as ih =>
      rw [LBTerm.mkApps] at h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (noFix_mkApps_head h).2
      · exact ih h x hx

/-! ### Distribution of de Bruijn ops over an application spine.

The implementation applies a (nullary) head to its arguments by a left fold of
`Expr.app` (`visitAppArgs`). These lemmas push `liftLooseBVars'`/`instantiate1'`
through that spine, used by the constructor/`casesOn` cases of the substitution
lemmas. -/

theorem liftLooseBVars'_foldl_app (s d : Nat) (f : Expr) (args : List Expr) :
    (args.foldl Expr.app f).liftLooseBVars' s d
      = (args.map (·.liftLooseBVars' s d)).foldl Expr.app (f.liftLooseBVars' s d) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => simp only [List.foldl, List.map, ih, Expr.liftLooseBVars']

theorem instantiate1'_foldl_app (e₀ : Expr) (d : Nat) (f : Expr) (args : List Expr) :
    (args.foldl Expr.app f).instantiate1' e₀ d
      = (args.map (·.instantiate1' e₀ d)).foldl Expr.app (f.instantiate1' e₀ d) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => simp only [List.foldl, List.map, ih, Expr.instantiate1']

/-- Re-wrap a `casesOn` alternative `(field-names, body)` as the lambda chain the
minor function erases to. Lets the `casesOn` rule reuse the `lam` rule for the
alternative's field binders. -/
def mkLambdas : List BinderName → LBTerm → LBTerm
  | [], body => body
  | n :: ns, body => .lambda n (mkLambdas ns body)

theorem shift_mkLambdas (d c : Nat) (names : List BinderName) (body : LBTerm) :
    LBTerm.shift d c (mkLambdas names body)
      = mkLambdas names (LBTerm.shift d (c + names.length) body) := by
  induction names generalizing c with
  | nil => rfl
  | cons n ns ih =>
      have h : c + (ns.length + 1) = (c + 1) + ns.length := by omega
      simp only [mkLambdas, LBTerm.shift, List.length_cons, h, ih]

theorem subst_mkLambdas (s : LBTerm) (d : Nat) (names : List BinderName) (body : LBTerm) :
    LBTerm.subst s d (mkLambdas names body)
      = mkLambdas names (LBTerm.subst s (d + names.length) body) := by
  induction names generalizing d with
  | nil => rfl
  | cons n ns ih =>
      have h : d + (ns.length + 1) = (d + 1) + ns.length := by omega
      simp only [mkLambdas, LBTerm.subst, List.length_cons, h, ih]

/-- **Inversion of lean4lean's `TrExprS` on a literal.** `TrExprS.lit` is the *only*
rule whose source is a `.lit`, and it translates the literal *through* its one-step
constructor unfolding `Literal.toConstructor`, to the **same** `VExpr`. So inverting is
total, cheap, and — unlike the projection case — involves no `sorry`-carrying lemma.
This is what makes the literal fragment's subject reduction `refl` (`SubjectReductionFull`)
and the simulation cases a plain appeal to the IH (`ErasesCorrectData`). -/
theorem TrExprS.lit_inv' {env : VEnv} {Us : List Name} {Δ : VLCtx} {l : Literal}
    {ve : VExpr} (h : TrExprS env Us Δ (.lit l) ve) :
    env.ContainsLits l ∧ TrExprS env Us Δ l.toConstructor ve := by
  cases h with | lit h1 h2 => exact ⟨h1, h2⟩

/--
Typed erasure relation between real `Lean.Expr` and `LBTerm`.

Parameters `env`/`Us`/`Γ` are fixed; the `VLCtx` is an index because binder rules
recurse under an extended context (mirroring `TrExprS.lam`/`letE`). `Γ` resolves
source `Name`s to target `Kername`s as before.
-/
inductive Erases (env : VEnv) (Us : List Name) (Γ : ErasureCtx) :
    VLCtx → Expr → LBTerm → Prop
  /-- Irrelevant subterms erase to `box`, witnessed by a real lean4lean typing
      derivation showing the term is a proof or a type-former. -/
  | box {Δ e ve}
      (htr : TrExprS env Us Δ e ve)
      (her : Erasable env Us.length Δ.toCtx ve) :
      Erases env Us Γ Δ e .box
  /-- **A literal**, modelled exactly as lean4lean models it (`TrExprS.lit`): `.lit l`
      erases to whatever its one-step constructor unfolding `l.toConstructor` erases to.
      Under `nat := .peano` that unfolding *is* the shipping `visitLiteral`
      (`Expr.natLitToConstructor`: `0 ↦ Nat.zero`, `n+1 ↦ Nat.succ (.lit (.natVal n))`),
      so the applied-form peano tower is produced by the existing `ctor_head`/`app` rules
      and the rule needs no new target-side machinery. `hcl` mirrors `TrExprS.lit`'s own
      premise and is free at every construction site (it falls out of the term's
      translation, via `TrExprS.lit_inv'`).

      **Why "unfold", not a dedicated `natTower` rule.** A rule
      `Erases Δ (.lit (.natVal n)) (natTower iid n)` would need its own de Bruijn
      inertness lemmas, its own inversion, its own semantics lemma and its own arity
      premises, and would *duplicate* the constructor rules. The unfolding rule composes
      with `ctor_head`/`app` (applied form, what shipping emits) **and** with `ctor`
      (block form) for free, and mirrors both `TrExprS.lit` and `visitLiteral`. It is
      literal-agnostic: `strVal` derivations exist but are never produced (shipping
      `panic!`s, and `Supported` excludes them), which costs nothing.

      Machine-`Nat` (`.prim`) stays **out of scope**: the relation has no `prim` rule, so
      the machine-mode statements are exactly as strong as before. -/
  | lit {Δ} {l : Literal} {t : LBTerm}
      (hcl : env.ContainsLits l)
      (h : Erases env Us Γ Δ l.toConstructor t) :
      Erases env Us Γ Δ (.lit l) t
  /-- **A structure projection** (projection round, slice P1). `visitProj`
      (`Erasure.lean`) looks the structure `S` up, registers it, and emits
      `.proj ⟨iid, numParams, i⟩` over the erased discriminant. The three `Γ` premises
      reproduce that lookup:
      * `hs` — `S` is a registered **structure** with `np` parameters (`Γ.projs`), which
        is `visitProj`'s `(indid, _) ← register_inductive indinfo` together with
        `indinfo.numParams`;
      * `hnfs` — its inductive has exactly **one** constructor, with `nf` retained fields
        (`Γ.ctorFields iid = some [nf]`). That singleton list *is*
        `register_inductive`'s own `is_struct` gate (`inf.ctors.length == 1`) expressed in
        data `Γ` already carries, and it is what makes the target rule's hard-wired
        constructor index `0` correct;
      * `hi` — the field index is in range, mirroring `TrProj`'s `i < fieldTys.length`.

      Like `Erases.cases`, only the discriminant is erased; the projection metadata is
      static. The target is `WcbvEval.proj`'s **non-block** flavour, which is the one
      `appliedFlags` runs (`with_constructor_as_block = false` kills `proj_block`,
      `with_prop_case = false` kills `proj_prop`).

      **No `TrExprS` premise**, and that is a deliberate divergence from `box`, `lam` and
      `letE`. Those carry one because they *record* a `VExpr` witness that later
      transports (the binder type, the `let` value, the erasable term); this rule's target
      carries no `VExpr`, and the source's translation is supplied at the use sites — the
      simulation gets it from its own `TrExprS` hypothesis, the strengthening lemma from
      `hwt`. Adding one would buy nothing and would cost an equational-uniqueness
      obligation that is *false* at `.proj`: `TrProj` pins `params`/`fieldTys` only up to
      definitional equality, which is why `TrProj.uniq` claims `IsDefEqU` and not equality.

      Note (pre-existing, inherited from `Erases.ctor`): shipping computes its field index
      *post*-argmask (`argmasks[0]![:i].toArray.count .keep`) and the model uses `i`, so
      like `Erases.ctor` — which relates a source spine to a target spine of the same
      length — this rule is exact when the argmask is all-`keep`. The parameter count is
      *not* mis-scaled by that: `register_inductive` builds its argmask over fields only,
      and `visitConstructor` emits the parameters unfiltered, so `np + i` indexes the
      target spine correctly at any mask. -/
  | proj {Δ} (S : Name) (i : Nat) (iid : InductiveId) (np nf : Nat)
      {e : Expr} {t : LBTerm}
      (hs : Γ.projs S = some (iid, np))
      (hnfs : Γ.ctorFields iid = some [nf])
      (hi : i < nf)
      (hd : Erases env Us Γ Δ e t) :
      Erases env Us Γ Δ (.proj S i e) (.proj ⟨iid, np, i⟩ t)
  | bvar {Δ} (i : Nat) :
      Erases env Us Γ Δ (.bvar i) (.bvar i)
  | fvar {Δ} (x : FVarId) :
      Erases env Us Γ Δ (.fvar x) (.fvar x)
  | const {Δ} (n : Name) (us : List Level) (kn : Kername)
      (h : Γ.constants n = kn)
      (hctor : Γ.ctors n = none) (hcases : Γ.casesOns n = none) :
      Erases env Us Γ Δ (.const n us) (.const kn)
  | app {Δ f f' a a'}
      (hf : Erases env Us Γ Δ f f') (ha : Erases env Us Γ Δ a a') :
      Erases env Us Γ Δ (.app f a) (.app f' a')
  | lam {Δ name ty bi b b'} {ty' : VExpr}
      (hty : TrExprS env Us Δ ty ty')
      (hb : Erases env Us Γ ((none, .vlam ty') :: Δ) b b') :
      Erases env Us Γ Δ (.lam name ty b bi) (.lambda (nameToBinder name) b')
  | letE {Δ name ty nd v v' b b'} {ty' val' : VExpr}
      (hty : TrExprS env Us Δ ty ty')
      (hval : TrExprS env Us Δ v val')
      (hv : Erases env Us Γ Δ v v')
      (hb : Erases env Us Γ ((none, .vlet ty' val') :: Δ) b b') :
      Erases env Us Γ Δ (.letE name ty v b nd) (.letIn (nameToBinder name) v' b')
  /-- A fully-applied constructor. The implementation emits `.construct iid cidx []`
      applied to its (filtered) args via `.app`; here we use the abstract
      args-inside `.construct iid cidx args'` (reusing `Semantics.lean`'s ι-rule).
      The source is the application spine `args.foldl Expr.app (.const cn us)`. The
      wrapping of the implementation's literal applied-`[]` output into this node is
      anchored in Half B's refinement. -/
  | ctor {Δ} (cn : Name) (us : List Level) (iid : InductiveId) (cidx : Nat)
      {args : List Expr} {args' : List LBTerm}
      (hc : Γ.ctors cn = some (iid, cidx))
      (hlen : args.length = args'.length)
      (hargs : ∀ i (h : i < args.length),
                 Erases env Us Γ Δ args[i] (args'[i]'(hlen ▸ h))) :
      Erases env Us Γ Δ (args.foldl Expr.app (.const cn us)) (.construct iid cidx args')
  /-- A **bare** constructor head, in *applied* form: a registered constructor name
      `.const cn us` erases to the empty-argument constructor node
      `.construct iid cidx []`, which the semantics' `construct_atom` treats as the
      base of a non-block (`appliedFlags`) constructor spine. This is what the
      shipping `visitConstApp` literally emits for a constructor head; the arguments
      are then wrapped by `Erases.app` (spine form), matching MetaRocq's non-block
      `eval_construct`. Kept alongside the abstract block `ctor` rule above. -/
  | ctor_head {Δ} (cn : Name) (us : List Level) (iid : InductiveId) (cidx : Nat)
      (hc : Γ.ctors cn = some (iid, cidx)) :
      Erases env Us Γ Δ (.const cn us) (.construct iid cidx [])
  /-- A `casesOn` application. The implementation (`visitCases`, `Erasure.lean:768`)
      erases only the discriminant and the minor functions, dropping the
      `casesInfo.discrPos` leading arguments (params/motive/indices), and turns each
      minor into an alternative `(field-names, body)` via `lambdaOrIntroToArity` +
      `mkAlt (filter argmask …)`. We model the minors with the normal relation by
      relating each to its alternative **re-wrapped** as a lambda chain
      (`mkLambdas`), so the `lam` rule handles the field binders. `pre` carries the
      dropped leading arguments (params/motive/indices).

      **Arity pins.** Three premises make the model's parse of a `casesOn` spine
      coincide with `visitCasesEtaGo`'s (which consumes exactly
      `casesInfo.arity = discrPos + 1 + #alts` arguments and appends the rest with
      `.app`):
      * `hpre` — `pre` is exactly the dropped prefix (`CasesInfo.discrPos`);
      * `hnlen` — one alternative per constructor (`nfs` is the inductive's
        per-constructor field-count list, `Γ.ctorFields`);
      * `harity` — alternative `j` binds exactly constructor `j`'s fields.

      Without them the relation strictly over-approximates the eraser and the ι
      forward simulation is false: an over-counted binder telescope (or, without
      `hpre`, an **over-applied** `casesOn` re-parsed with the first minor as
      discriminant) erases to a `.case` that `WcbvEval` cannot step — there is no
      `case_cong` rule, so a `.case` on a `.lambda` discriminant is stuck. See §C3 in
      `SubjectReductionIota.lean`.

      Note (pre-existing, inherited from `Erases.ctor`): `nfs` records the *retained*
      (post-argmask) field counts, and the model does not represent argmask filtering
      — `Erases.ctor` relates a source spine to a target spine of the same length. The
      two coincide exactly when the argmask is all-`keep`. -/
  | cases {Δ} (con : Name) (us : List Level) (iid : InductiveId) (numParams : Nat)
      (pre : List Expr)
      {discr : Expr} {discr' : LBTerm}
      {minors : List Expr} {alts' : List (List BinderName × LBTerm)}
      {nfs : List Nat}
      (hc : Γ.casesOns con = some (iid, numParams))
      (hpre : Γ.casesDiscrPos con = some pre.length)
      (hnfs : Γ.ctorFields iid = some nfs)
      (hd : Erases env Us Γ Δ discr discr')
      (hlen : minors.length = alts'.length)
      (hnlen : alts'.length = nfs.length)
      (harity : ∀ j (h : j < alts'.length),
                  (alts'[j]'h).1.length = nfs[j]'(hnlen ▸ h))
      (halts : ∀ j (h : j < minors.length),
                 Erases env Us Γ Δ minors[j]
                   (mkLambdas (alts'[j]'(hlen ▸ h)).1 (alts'[j]'(hlen ▸ h)).2)) :
      Erases env Us Γ Δ
        ((discr :: minors).foldl Expr.app (pre.foldl Expr.app (.const con us)))
        (.case (iid, numParams) discr' alts')
  /-- **The fixvar leaf** (recursion wall, slice W3.1). Models `visitConst`'s
      `return .fvar id` (`Erasure.lean`): while a mutual block is being erased, a
      reference to one of the block's *own* names is replaced by the fresh `FVarId` the
      run minted for that sibling, and `mkDef`/`closeFix` later binds those fvars into
      the block's de Bruijn binders. Only usable at a `Γ` that has a fixvar map
      installed; every top-level `Γ` has `fixvars = fun _ => none`, so `Erases.const_inv`'s
      fixvar disjunct is killed by `rfl`/`simp` there — which is what the `hnfv` premise
      of the forward simulations does.

      `hctor`/`hcases` mirror `Erases.const`'s (and `const_fix`'s) disjointness premises.
      They are faithful: `visitConstApp` dispatches `getCasesInfo?`/`getCtorArity?`
      *before* falling through to `visitConst`, so a name that reaches the fixvar branch
      is neither a registered `casesOn` nor a registered constructor. They are what lets
      `ctor_spine_inv`/`cases_spine_inv` refute this leaf at a registered head.

      **`hfresh` — the freshness premise, and why it is on the rule.** The target of this
      rule *is* an fvar, so — unlike every other leaf — it is not inert under
      `toBvar`. `Erases.abstract` (`ErasesAbstract`) closes the target over a binder's
      fvar `v₀` while leaving the source `.const nm us` alone, so the arm is derivable
      only when `toBvar v₀ dk (.fvar x) = .fvar x`, i.e. when `x ≠ v₀`. `hfresh` supplies
      exactly that: `v₀ ∈ Δ₁.fvars` by `VLCtx.Abstract.fvars_eq`, and `x` is fresh for
      `Δ₁`. It is *self-transporting* — `VLCtx.Abstract`/`BVLift`/`InstN`/`InstLet` all
      come with an `fvars_eq` lemma, so each of the six enumerated inductions
      re-establishes it at its conclusion context from the same lemma that discharges the
      arm. Semantically it is the run's own freshness discipline: `visitMutual` mints the
      block's fixvars *before* `visitExpr` opens any binder, so no fixvar is ever a
      `Δ`-entry (this is `BridgeInv.fixfresh`).

      The alternative — a freshness side condition on `Erases.abstract` itself — was
      rejected in slice W2: it ripples through `Erases.uninstantiate` into `Bridge`'s two
      binder lemmas and `VisitExprRefines`, where the rule-side premise ripples nowhere. -/
  | fixvar {Δ} (nm : Name) (us : List Level) (x : FVarId)
      (h : Γ.fixvars nm = some x)
      (hctor : Γ.ctors nm = none) (hcases : Γ.casesOns nm = none)
      (hfresh : x ∉ Δ.fvars) :
      Erases env Us Γ Δ (.const nm us) (.fvar x)
  /-- **The recursive-constant leaf** (recursion wall, slice W1). A constant that `Γ`
      records as recursive relates to *its own* `.fix` node. This is **not** what the
      eraser emits at a call site — there it emits `.const kn`, handled by `Erases.const`,
      and the target reaches the block by `WcbvEval.delta` — so `Erases` is deliberately
      non-deterministic at a recursive constant. The rule exists because a fix
      *unfolding* (`WcbvEval.fix_guarded`'s `substList (fixSubst defs)`) puts
      `.fix defs j` exactly where the source has the sibling `.const nⱼ`; §4.1 of the
      recursion design shows no arrangement of `fix`'s premises avoids needing it.

      `hctor`/`hcases` mirror `Erases.const`'s disjointness premises, and are what lets
      `ctor_spine_inv`/`cases_spine_inv` refute this leaf at a registered
      constructor/`casesOn` head. The three LBTerm-side inertness equalities are carried
      exactly as in `fix`, so the transport metatheory reuses them verbatim. -/
  | const_fix {Δ} (nm : Name) (us : List Level)
      {defs : List (@FixDef LBTerm)} {idx : Nat}
      (h : Γ.recBodies nm = some (defs, idx))
      (hctor : Γ.ctors nm = none) (hcases : Γ.casesOns nm = none)
      (hshift : ∀ (d c : Nat), LBTerm.shift d c (.fix defs idx) = .fix defs idx)
      (hsubst : ∀ (s : LBTerm) (d : Nat), LBTerm.subst s d (.fix defs idx) = .fix defs idx)
      (htobv : ∀ (x : FVarId) (l : Nat), toBvar x l (.fix defs idx) = .fix defs idx) :
      Erases env Us Γ Δ (.const nm us) (.fix defs idx)
  /-- **Environment-level mutual `fix` (P3; re-founded by the recursion wall, W1).**
      Lean has no fixpoint node — recursion is created at the environment level by
      `visitMutual` (`Erasure.lean`), which erases each recursive def body with its
      sibling `.const`s mapped to fresh fvars, closes the result with `mkDef`
      (`closeFix`), and emits a `.fix defs j` decl per name of the block. This rule
      reconstructs that: `nms`/`srcs` are the block's names and their **real** source
      bodies, `defs` the emitted block, and the conclusion says the `idx`-th body — pinned
      to it by `hsrc`, and syntactically `.lam`-headed as every `_unsafe_rec` body is —
      erases to `.fix defs idx`.

      **What `hbodies` says, and why in unfolded form.** Sibling `j`'s source body erases
      to the *one-step unfolding* of def `j`, i.e. to
      `substList (fixSubst defs) defs[j].body` — exactly the reduct
      `WcbvEval.fix_guarded` produces. Two remarks:

      * This is finite, not circular, precisely because of the `const_fix` leaf above:
        the source's self-references are `.const nⱼ`, which the leaf sends to `.fix defs j`
        in one step without descending into the block again. (For a *contentless* block
        like `fix f. f` the premise does degenerate into its own conclusion and no
        derivation exists — correctly, since nothing erases to that block.)
      * The design's formulation — `hbodies` in *fvar-open* form under the block's
        fixvar-extended context `Γ.withFixvars nms ids` — is **not expressible**: `Γ` is a
        *parameter* of this inductive, so no constructor premise may mention `Erases` at a
        different `Γ`. The two are related by the (deferred) `Erases.instFixvars`
        transport, which is exactly the open→unfolded direction; stating the rule in the
        unfolded form moves that obligation from the rule's *consumers* (the forward
        simulation, which wants the unfolding and nothing else) to its *producers*
        (`erases_fix_of_closed`, where `closeFix_substList_fixSubst` discharges the
        `mkDef`-closing half of it today).

      **What the premises pin.**
      * `hsrc` — the missing link the pre-W1 rule lacked: without it `n ty b bi` occurred
        only in the inertness equalities and the conclusion, so *any* closed fvar-free
        `.lam` erased to *any* closed block (see the machine-checked record in
        `EnvErasureRec`, `erases_correct_data_without_noFix_false_of_contentless_fix`).
      * `hreg` — the block is self-describing: `Γ` records it for each of its own names,
        which is what makes the `const_fix` leaf available for the sibling references
        inside `hbodies`.
      * `hrarg` — every def's `principalArgIdx` is `0`. `mkDef` never sets it
        (`Basic.lean`'s default), and the whole source-β ↔ target-`fix_guarded`+`beta`
        correspondence rests on it: with a non-zero `rarg` a partially applied recursive
        function is a *stuck fix spine* on the target and a plain λ value on the source.
        Carried so that the shipping TODO "eta-expand fixpoints?" breaks this loudly
        rather than silently.
      * `hlift`/`hinst`/`habsl`/`hshift`/`hsubst`/`htobv` — the block is **closed** and
        fvar-free (top-level recursive defs are), so every de-Bruijn op is the identity on
        the source `.lam` and the target `.fix`. That is what makes the transport
        metatheory (`erases_shift`/`erases_subst`/`Erases.abstract`/`thin_vlet`) reuse the
        fix fields verbatim — no `fixExtend` cutoff bookkeeping. `hbodies` is `∀ Δf`, so it
        transports for free too (and the conclusion's `Δ` stays free, which is the
        context-uniformity `ErasesEnvDelta` needs). -/
  | fix {Δ : VLCtx} (idx : Nat)
      {n : Name} {ty b : Expr} {bi : BinderInfo}
      {nms : List Name} {srcs : List Expr}
      {defs : List (@FixDef LBTerm)}
      (hidx : idx < defs.length)
      (hnlen : nms.length = defs.length)
      (hslen : srcs.length = defs.length)
      (hsrc : (srcs[idx]'(hslen ▸ hidx)) = .lam n ty b bi)
      (hreg : ∀ j (h : j < defs.length), Γ.recBodies (nms[j]'(hnlen ▸ h)) = some (defs, j))
      (hrarg : ∀ d ∈ defs, d.principalArgIdx = 0)
      (hlift : ∀ (s d : Nat), (Expr.lam n ty b bi).liftLooseBVars' s d = .lam n ty b bi)
      (hinst : ∀ (e₀ : Expr) (d : Nat), (Expr.lam n ty b bi).instantiate1' e₀ d = .lam n ty b bi)
      (habsl : ∀ (v : FVarId) (d : Nat), (Expr.lam n ty b bi).abstract1 v d = .lam n ty b bi)
      (hshift : ∀ (d c : Nat), LBTerm.shift d c (.fix defs idx) = .fix defs idx)
      (hsubst : ∀ (s : LBTerm) (d : Nat), LBTerm.subst s d (.fix defs idx) = .fix defs idx)
      (htobv : ∀ (x : FVarId) (l : Nat), toBvar x l (.fix defs idx) = .fix defs idx)
      (hbodies : ∀ j (h : j < defs.length) (Δf : VLCtx),
          Erases env Us Γ Δf (srcs[j]'(hslen ▸ h))
            (LBTerm.substList (LBTerm.fixSubst defs) (defs[j]'h).body)) :
      Erases env Us Γ Δ (.lam n ty b bi) (.fix defs idx)

/-! ### Erasure commutes with de Bruijn weakening (step A2.2).

Mirrors lean4lean's `TrExprS.weakBV`: lifting the source `Expr` by
`liftLooseBVars'` matches lifting the target `LBTerm` by `shift`, under a
`VLCtx.BVLift` weakening of the context. The `box`/`lam`/`letE` cases reuse
`weakBV`/`Erasable.weakN` for their `TrExprS`/`Erasable` premises; the rest is
structural index bookkeeping (the conventions align: source `if i < dk then i
else i + dn` equals `LBTerm.shift dn dk`). -/
theorem erases_shift {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Γ : ErasureCtx} {Δ Δ' : VLCtx} {dn dk n k : Nat}
    (W : VLCtx.BVLift Δ Δ' dn dk n k)
    {e : Expr} {t : LBTerm} (h : Erases env Us Γ Δ e t) :
    Erases env Us Γ Δ' (e.liftLooseBVars' dk dn) (LBTerm.shift dn dk t) := by
  induction h generalizing Δ' dk k with
  | box htr her => exact .box (htr.weakBV henv W) (her.weakN henv W.toCtx)
  | lit hcl _ ih =>
    -- `liftLooseBVars'` is the identity on `.lit`, and on the (closed) unfolding.
    refine .lit hcl (Expr.liftLooseBVars_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | proj S i iid np nf hs hnfs hi _ ihd => exact .proj S i iid np nf hs hnfs hi (ihd W)
  | bvar i =>
    simp only [Expr.liftLooseBVars', LBTerm.shift]
    by_cases hlt : i < dk
    · rw [if_pos hlt, if_neg (by omega : ¬ i ≥ dk)]; exact .bvar i
    · rw [if_neg hlt, if_pos (by omega : i ≥ dk)]; exact .bvar (i + dn)
  | fvar x => exact .fvar x
  | const n us kn h hctor hcases => exact .const n us kn h hctor hcases
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | lam hty _ ihb => exact .lam (hty.weakBV henv W) (ihb (W.cons _))
  | letE hty hval _ _ ihv ihb =>
      exact .letE (hty.weakBV henv W) (hval.weakBV henv W) (ihv W) (ihb (W.cons _))
  | ctor cn us iid cidx hc hlen _ ihargs =>
      simp only [liftLooseBVars'_foldl_app, Expr.liftLooseBVars', LBTerm.shift,
                 LBTerm.shiftArgs_eq_map]
      refine .ctor cn us iid cidx hc (by simp [hlen]) (fun i hi => ?_)
      rw [List.getElem_map, List.getElem_map]
      exact ihargs i (by simpa using hi) W
  | ctor_head cn us iid cidx hc =>
      simp only [Expr.liftLooseBVars', LBTerm.shift, LBTerm.shiftArgs]
      exact .ctor_head cn us iid cidx hc
  | @cases _ con us iid numParams pre discr discr' minors alts' nfs hc hpre hnfs _
      hlen hnlen harity _ ihd ihalts =>
      simp only [liftLooseBVars'_foldl_app, List.map_cons,
                 Expr.liftLooseBVars', LBTerm.shift, LBTerm.shiftAlts_eq_map]
      refine .cases con us iid numParams (pre.map (·.liftLooseBVars' dk dn)) hc
        (by simpa using hpre) hnfs (ihd W)
        (minors := minors.map (·.liftLooseBVars' dk dn))
        (alts' := alts'.map (fun a => (a.1, LBTerm.shift dn (dk + a.1.length) a.2)))
        (by simpa using hlen) (by simpa using hnlen)
        (fun j hj => by rw [List.getElem_map]; exact harity j (by simpa using hj))
        (fun j hj => ?_)
      rw [List.getElem_map, List.getElem_map, ← shift_mkLambdas]
      exact ihalts j (by simpa using hj) W
  | fixvar nm us x hfx hctor hcases hfresh =>
      -- `liftLooseBVars'`/`shift` are both the identity here; freshness travels along
      -- `BVLift.fvars_eq`.
      exact .fixvar nm us x hfx hctor hcases (W.fvars_eq ▸ hfresh)
  | const_fix nm us hrec hctor hcases hshift hsubst htobv =>
      -- The registered block is closed: `shift` is the identity on it.
      rw [hshift dn dk]
      exact .const_fix nm us hrec hctor hcases hshift hsubst htobv
  | @fix Δc idx nm tty tb tbi nms srcs defs hidx hnlen hslen hsrc hreg hrarg
      hlift hinst habsl hshift hsubst htobv hbodies _ihb =>
      -- The fix source/target are closed & fvar-free (top-level rec def): both de
      -- Bruijn ops are the identity (the inertness premises), so the fix fields
      -- transport verbatim (no `fixExtend` cutoff bookkeeping — cf. design §7).
      rw [hlift dk dn, hshift dn dk]
      exact .fix idx hidx hnlen hslen hsrc hreg hrarg hlift hinst habsl hshift hsubst htobv
        hbodies

/-- A `VLCtx.InstN` witness yields the de Bruijn weakening of the substitutee's
context `Δ₀` into the instantiated context `Δ` (it gained `dk` binders). Used to
lift the substitutee's erasure in the `bvar i = dk` case of `erases_subst`. -/
theorem instN_toBVLift {Δ₀ Δ₁ Δ : VLCtx} {e₀' A₀ : VExpr} {dk k : Nat}
    (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) : VLCtx.BVLift Δ₀ Δ dk 0 k 0 := by
  induction W with
  | zero => exact .refl
  | @succ _ k _ _ d _ ih => cases d <;> exact ih.skip _

/-! ### Erasure commutes with substitution (step A2.3).

Mirrors lean4lean's `TrExprS.instN`: source `Expr.instantiate1'` ↔ target
`LBTerm.subst` under a `VLCtx.InstN`. `box`/`lam`/`letE` discharge their
`TrExprS`/`Erasable` premises via `instN`/`Erasable.inst`; the `bvar = dk` case
lifts the substitutee via `erases_shift` (using `InstN.toBVLift`). -/
theorem erases_subst {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Γ : ErasureCtx} {Δ₀ : VLCtx} {e₀ : Expr} {e₀' A₀ : VExpr} {s' : LBTerm}
    (ht₀ : TrExprS env Us Δ₀ e₀ e₀')
    (t₀ : env.HasType Us.length Δ₀.toCtx e₀' A₀)
    (h₀ : Erases env Us Γ Δ₀ e₀ s')
    {Δ₁ Δ : VLCtx} {dk k : Nat} (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ)
    {e : Expr} {t : LBTerm} (h : Erases env Us Γ Δ₁ e t) :
    Erases env Us Γ Δ (e.instantiate1' e₀ dk) (LBTerm.subst s' dk t) := by
  induction h generalizing Δ dk k with
  | box htr her =>
      exact .box (TrExprS.instN henv ht₀ t₀ W htr) (her.inst henv W.toCtx t₀)
  | lit hcl _ ih =>
      -- `instantiate1'` is the identity on `.lit`, and on the (closed) unfolding.
      refine .lit hcl (Expr.instantiate1'_eq_self ?_ ▸ ih W :)
      exact Closed.toConstructor.looseBVarRange_le
  | proj S i iid np nf hs hnfs hi _ ihd => exact .proj S i iid np nf hs hnfs hi (ihd W)
  | bvar i =>
      simp only [Expr.instantiate1', LBTerm.subst]
      split <;> rename_i h
      · exact .bvar i
      · split <;> rename_i h2
        · exact erases_shift henv (instN_toBVLift W) h₀
        · exact .bvar (i - 1)
  | fvar x => exact .fvar x
  | const n us kn h hctor hcases => exact .const n us kn h hctor hcases
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | lam hty _ ihb =>
      exact .lam (TrExprS.instN henv ht₀ t₀ W hty) (ihb (W.succ (d := .vlam _)))
  | letE hty hval _ _ ihv ihb =>
      exact .letE (TrExprS.instN henv ht₀ t₀ W hty) (TrExprS.instN henv ht₀ t₀ W hval)
        (ihv W) (ihb (W.succ (d := .vlet ..)))
  | ctor cn us iid cidx hc hlen _ ihargs =>
      simp only [instantiate1'_foldl_app, Expr.instantiate1', LBTerm.subst,
                 LBTerm.substArgs_eq_map]
      refine .ctor cn us iid cidx hc (by simp [hlen]) (fun i hi => ?_)
      rw [List.getElem_map, List.getElem_map]
      exact ihargs i (by simpa using hi) W
  | ctor_head cn us iid cidx hc =>
      simp only [Expr.instantiate1', LBTerm.subst, LBTerm.substArgs]
      exact .ctor_head cn us iid cidx hc
  | @cases _ con us iid numParams pre discr discr' minors alts' nfs hc hpre hnfs _
      hlen hnlen harity _ ihd ihalts =>
      simp only [instantiate1'_foldl_app, List.map_cons,
                 Expr.instantiate1', LBTerm.subst, LBTerm.substAlts_eq_map]
      refine .cases con us iid numParams (pre.map (·.instantiate1' e₀ dk)) hc
        (by simpa using hpre) hnfs (ihd W)
        (minors := minors.map (·.instantiate1' e₀ dk))
        (alts' := alts'.map (fun a => (a.1, LBTerm.subst s' (dk + a.1.length) a.2)))
        (by simpa using hlen) (by simpa using hnlen)
        (fun j hj => by rw [List.getElem_map]; exact harity j (by simpa using hj))
        (fun j hj => ?_)
      rw [List.getElem_map, List.getElem_map, ← subst_mkLambdas]
      exact ihalts j (by simpa using hj) W
  | fixvar nm us x hfx hctor hcases hfresh =>
      -- `instantiate1'`/`subst` are both the identity here; `InstN.fvars_eq` moves the
      -- freshness from `Δ₁` to `Δ` (both agree with `Δ₀`).
      obtain ⟨h1, h2⟩ := W.fvars_eq
      exact .fixvar nm us x hfx hctor hcases (h2 ▸ h1 ▸ hfresh)
  | const_fix nm us hrec hctor hcases hshift hsubst htobv =>
      rw [hsubst s' dk]
      exact .const_fix nm us hrec hctor hcases hshift hsubst htobv
  | @fix Δc idx nm tty tb tbi nms srcs defs hidx hnlen hslen hsrc hreg hrarg
      hlift hinst habsl hshift hsubst htobv hbodies _ihb =>
      rw [hinst e₀ dk, hsubst s' dk]
      exact .fix idx hidx hnlen hslen hsrc hreg hrarg hlift hinst habsl hshift hsubst htobv
        hbodies

/-! ### Non-vacuity guard for `Erases.lit`

`Erases.lit` is easy to render *vacuous*: `hcl` needs an `env` that really declares
`Nat`, and the unfolding's `ctor_head` steps need a `Γ` that really registers `Nat`'s two
constructors. Both are **constructed** below (nothing is assumed), and the guard exhibits
the literal `2` erasing to

    T 2 = .app (.construct natLitInd 1 []) (.app (.construct natLitInd 1 [])
            (.construct natLitInd 0 []))

which is *exactly* the applied-form peano tower the shipping eraser emits for
`(2 : Nat)` under `nat := .peano`. The context data is shared with the source-side /
target-side literal guards downstream (`ErasesCorrectData.lean`), so it is public. -/

/-- A minimal `VEnv` declaring `Nat` — enough to *prove* `VEnv.ContainsLits (.natVal n)`,
which is `TrExprS.lit`'s (and `Erases.lit`'s) premise. -/
noncomputable def envNatLit : VEnv :=
  (VEnv.empty.addConst ``Nat ⟨0, .sort (.succ .zero)⟩).getD .empty

theorem envNatLit_Nat : envNatLit.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩ := by
  unfold envNatLit VEnv.addConst VEnv.empty; simp

theorem envNatLit_containsLits (n : Nat) : envNatLit.ContainsLits (.natVal n) :=
  ⟨_, envNatLit_Nat⟩

/-- The target-side `InductiveId` `register_inductive` would assign to `Nat`. -/
def natLitInd : InductiveId := ⟨toKername ``Nat, 0⟩

/-- A concrete `Γ` in **peano** mode registering `Nat`'s two constructors at their real
kernel indices and arities (`Nat.zero ↦ cidx 0, arity 0`; `Nat.succ ↦ cidx 1, arity 1` —
both verified against the kernel: `numParams = 0`, `numFields = 0`/`1`). -/
def ΓnatLit : ErasureCtx where
  inductives := fun n => if n = ``Nat then some natLitInd else none
  constants := toKername
  ctors := fun n =>
    if n = ``Nat.zero then some (natLitInd, 0)
    else if n = ``Nat.succ then some (natLitInd, 1) else none
  ctorArities := fun n =>
    if n = ``Nat.zero then some 0 else if n = ``Nat.succ then some 1 else none
  ctorFields := fun _ => some [0, 1]
  natPeano := true

theorem ΓnatLit_zero : ΓnatLit.ctors ``Nat.zero = some (natLitInd, 0) := by
  simp [ΓnatLit]

theorem ΓnatLit_succ : ΓnatLit.ctors ``Nat.succ = some (natLitInd, 1) := by
  simp [ΓnatLit]

theorem ΓnatLit_arity_zero : ΓnatLit.ctorArities ``Nat.zero = some 0 := by
  simp [ΓnatLit]

theorem ΓnatLit_arity_succ : ΓnatLit.ctorArities ``Nat.succ = some 1 := by
  simp [ΓnatLit]

theorem ΓnatLit_ctors_other {n : Name} (h0 : n ≠ ``Nat.zero) (h1 : n ≠ ``Nat.succ) :
    ΓnatLit.ctors n = none := by
  simp [ΓnatLit, h0, h1]

/-- The peano tower `T n` the shipping `visitLiteral` emits in applied form:
`T 0 = .construct natLitInd 0 []`, `T (n+1) = .app (.construct natLitInd 1 []) (T n)`. -/
def natLitTower : Nat → LBTerm
  | 0 => .construct natLitInd 0 []
  | n + 1 => .app (.construct natLitInd 1 []) (natLitTower n)

/-- **Non-vacuity (`Erases.lit`), at every `n`**: the literal `n` erases to the peano
tower, by `lit` composing with the existing `app`/`ctor_head` rules — no new target-side
machinery. -/
theorem erases_natLit (Us : List Name) (Δ : VLCtx) :
    ∀ n : Nat, Erases envNatLit Us ΓnatLit Δ (.lit (.natVal n)) (natLitTower n)
  | 0 => .lit (envNatLit_containsLits 0)
      (.ctor_head ``Nat.zero [] natLitInd 0 ΓnatLit_zero)
  | n + 1 => .lit (envNatLit_containsLits (n + 1))
      (.app (.ctor_head ``Nat.succ [] natLitInd 1 ΓnatLit_succ) (erases_natLit Us Δ n))

/-- The concrete instance the design pins: `2` erases to the three-node tower. -/
example (Us : List Name) (Δ : VLCtx) :
    Erases envNatLit Us ΓnatLit Δ (.lit (.natVal 2))
      (.app (.construct natLitInd 1 [])
        (.app (.construct natLitInd 1 []) (.construct natLitInd 0 []))) :=
  erases_natLit Us Δ 2

/-! ### Non-vacuity for `Erases.proj` (projection round, slice P1)

The rule is guarded at both polarities, which is what the development asks of every
hypothesis-bearing rule. The fixture is the shape `register_inductive`'s `is_struct` gate
admits and the one the target-side metatheory already uses (`AC`,
`Semantics/Metatheory.lean`: one parameter, one constructor `mk`, one field, not
recursive), rebuilt here as a `Γ` because `Erases` needs no `GlobalDeclarations`. Its
non-degeneracy matters: `ctorArities = 2 = 1 param + 1 field`, so a rule that confused
`paramCount` with `fieldIdx` would produce a different `ProjectionInfo`. -/

/-- The target-side `InductiveId` `register_inductive` would assign to the structure
`AC`. -/
def projInd : InductiveId := ⟨toKername `AC, 0⟩

/-- A concrete `Γ` registering the one-parameter, one-field structure `AC`: the structure
name under `projs` (with its parameter count), its single constructor `AC.mk` at index
`0` with arity `1 + 1`, and the field-count list `[1]` — the singleton that *is*
`is_struct`'s `inf.ctors.length == 1`. -/
def Γproj : ErasureCtx where
  inductives := fun n => if n = `AC then some projInd else none
  constants := toKername
  ctors := fun n => if n = `AC.mk then some (projInd, 0) else none
  ctorArities := fun n => if n = `AC.mk then some 2 else none
  ctorFields := fun _ => some [1]
  projs := fun n => if n = `AC then some (projInd, 1) else none

theorem Γproj_projs : Γproj.projs `AC = some (projInd, 1) := by simp [Γproj]
theorem Γproj_ctorFields : Γproj.ctorFields projInd = some [1] := rfl
theorem Γproj_ctors : Γproj.ctors `AC.mk = some (projInd, 0) := by simp [Γproj]
theorem Γproj_arity : Γproj.ctorArities `AC.mk = some 2 := by simp [Γproj]

/-- **Non-vacuity (`Erases.proj`), positive.** Field `0` of a registered structure erases
to `.proj ⟨projInd, 1, 0⟩` over the erased discriminant — here a free variable, so the
sub-derivation is `Erases.fvar` and nothing about the environment is needed. -/
theorem erases_proj_fvar {env : VEnv} (Us : List Name) (Δ : VLCtx) (x : FVarId) :
    Erases env Us Γproj Δ (.proj `AC 0 (.fvar x)) (.proj ⟨projInd, 1, 0⟩ (.fvar x)) :=
  .proj `AC 0 projInd 1 1 Γproj_projs Γproj_ctorFields (by omega) (.fvar x)

/-- …and at a **compound** discriminant, so the sub-derivation is doing work: the
structure's own constructor applied to its parameter and its field, in the applied form
the shipping eraser emits. This is the redex the projection simulation will step. -/
theorem erases_proj_ctor {env : VEnv} (Us : List Name) (Δ : VLCtx) (x y : FVarId) :
    Erases env Us Γproj Δ
      (.proj `AC 0 ([Expr.fvar x, .fvar y].foldl Expr.app (.const `AC.mk [])))
      (.proj ⟨projInd, 1, 0⟩
        (.app (.app (.construct projInd 0 []) (.fvar x)) (.fvar y))) :=
  .proj `AC 0 projInd 1 1 Γproj_projs Γproj_ctorFields (by omega)
    (.app (.app (.ctor_head `AC.mk [] projInd 0 Γproj_ctors) (.fvar x)) (.fvar y))

/-! ### The literal's own **translation** (Nat-literals wall, L4)

`envNatLit` declares just enough to *prove* `ContainsLits`, which is all `TrExprS.lit`
and `Erases.lit` ask for. The bridge asks for more: its hypothesis is
`∃ ve, TrExprS env Us Δ (.lit l) ve`, and a literal's translation goes *through* its
unfolding — a `Nat.succ` spine. So a constructed witness needs `Nat`'s two constructors
declared **and typed**, which `envNatT` does, in the `envFO` idiom (`FirstOrder.lean`):
three axioms, `Nat : Sort 1`, `Nat.zero : Nat`, `Nat.succ : Nat → Nat`.

Kept separate from `envNatLit` so the L1/L2 guards keep their minimal environment. -/

/-- Stage 1 of `envNatT`: `Nat : Sort 1`. -/
noncomputable def envNatT₀ : VEnv :=
  (VEnv.empty.addConst ``Nat ⟨0, .sort (.succ .zero)⟩).getD .empty
/-- Stage 2 of `envNatT`: `Nat.zero : Nat`. -/
noncomputable def envNatT₁ : VEnv :=
  (envNatT₀.addConst ``Nat.zero ⟨0, .const ``Nat []⟩).getD .empty
/-- `envNatLit` with `Nat`'s two constructors added as typed axioms — the smallest `VEnv`
in which a `Nat` literal's own `TrExprS` witness is constructible. -/
noncomputable def envNatT : VEnv :=
  (envNatT₁.addConst ``Nat.succ ⟨0, .forallE (.const ``Nat []) (.const ``Nat [])⟩).getD .empty

theorem envNatT₀_add : VEnv.empty.addConst ``Nat ⟨0, .sort (.succ .zero)⟩ = some envNatT₀ := by
  unfold envNatT₀ VEnv.addConst VEnv.empty; simp
theorem envNatT₁_add : envNatT₀.addConst ``Nat.zero ⟨0, .const ``Nat []⟩ = some envNatT₁ := by
  unfold envNatT₁ envNatT₀ VEnv.addConst VEnv.empty; simp
theorem envNatT_add :
    envNatT₁.addConst ``Nat.succ ⟨0, .forallE (.const ``Nat []) (.const ``Nat [])⟩
      = some envNatT := by
  unfold envNatT envNatT₁ envNatT₀ VEnv.addConst VEnv.empty; simp

theorem envNatT₀_Nat : envNatT₀.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩ := by
  unfold envNatT₀ VEnv.addConst VEnv.empty; simp
theorem envNatT₁_Nat : envNatT₁.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩ := by
  unfold envNatT₁ envNatT₀ VEnv.addConst VEnv.empty; simp
theorem envNatT_Nat : envNatT.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩ := by
  unfold envNatT envNatT₁ envNatT₀ VEnv.addConst VEnv.empty; simp
theorem envNatT_zero : envNatT.constants ``Nat.zero = some ⟨0, .const ``Nat []⟩ := by
  unfold envNatT envNatT₁ envNatT₀ VEnv.addConst VEnv.empty; simp
theorem envNatT_succ :
    envNatT.constants ``Nat.succ
      = some ⟨0, .forallE (.const ``Nat []) (.const ``Nat [])⟩ := by
  unfold envNatT envNatT₁ envNatT₀ VEnv.addConst VEnv.empty; simp

theorem envNatT_containsLits (n : Nat) : envNatT.ContainsLits (.natVal n) :=
  ⟨_, envNatT_Nat⟩

/-- `envNatT` is well-formed (three axioms, each typed in the preceding stage). -/
theorem envNatT_wf : envNatT.WF := by
  have hNat : VConstant.WF VEnv.empty ⟨0, .sort (.succ .zero)⟩ :=
    ⟨.succ (.succ .zero), VEnv.IsDefEq.sortDF (by trivial) (by trivial) (by rfl)⟩
  have hzero : VConstant.WF envNatT₀ ⟨0, .const ``Nat []⟩ := by
    refine ⟨.succ .zero, ?_⟩
    exact VEnv.IsDefEq.constDF (env := envNatT₀) (uvars := 0) (Γ := []) (c := ``Nat)
      (ci := ⟨0, .sort (.succ .zero)⟩) (ls := []) (ls' := []) envNatT₀_Nat
      (by simp) (by simp) (by simp) (by simp)
  have hNat₁ : envNatT₁.HasType 0 [] (.const ``Nat []) (.sort (.succ .zero)) :=
    VEnv.IsDefEq.constDF (env := envNatT₁) (uvars := 0) (Γ := []) (c := ``Nat)
      (ci := ⟨0, .sort (.succ .zero)⟩) (ls := []) (ls' := []) envNatT₁_Nat
      (by simp) (by simp) (by simp) (by simp)
  have hNat₁' : envNatT₁.HasType 0 [.const ``Nat []] (.const ``Nat []) (.sort (.succ .zero)) :=
    VEnv.IsDefEq.constDF (env := envNatT₁) (uvars := 0) (Γ := [.const ``Nat []]) (c := ``Nat)
      (ci := ⟨0, .sort (.succ .zero)⟩) (ls := []) (ls' := []) envNatT₁_Nat
      (by simp) (by simp) (by simp) (by simp)
  have hsucc : VConstant.WF envNatT₁ ⟨0, .forallE (.const ``Nat []) (.const ``Nat [])⟩ :=
    ⟨_, VEnv.IsDefEq.forallEDF hNat₁ hNat₁'⟩
  exact ⟨[.axiom ⟨⟨0, .forallE (.const ``Nat []) (.const ``Nat [])⟩, ``Nat.succ⟩,
          .axiom ⟨⟨0, .const ``Nat []⟩, ``Nat.zero⟩,
          .axiom ⟨⟨0, .sort (.succ .zero)⟩, ``Nat⟩],
    .decl (.axiom hsucc envNatT_add)
      (.decl (.axiom hzero envNatT₁_add) (.decl (.axiom hNat envNatT₀_add) .empty))⟩

/-- The `VExpr` a peano literal translates to: the same tower, one `Nat.succ` per step. -/
def vNatTower : Nat → VExpr
  | 0 => .const ``Nat.zero []
  | n + 1 => .app (.const ``Nat.succ []) (vNatTower n)

theorem envNatT_zeroType : envNatT.HasType 0 [] (.const ``Nat.zero []) (.const ``Nat []) :=
  VEnv.IsDefEq.constDF (env := envNatT) (uvars := 0) (Γ := []) (c := ``Nat.zero)
    (ci := ⟨0, .const ``Nat []⟩) (ls := []) (ls' := []) envNatT_zero
    (by simp) (by simp) (by simp) (by simp)

theorem envNatT_succType : envNatT.HasType 0 []
    (.const ``Nat.succ []) (.forallE (.const ``Nat []) (.const ``Nat [])) :=
  VEnv.IsDefEq.constDF (env := envNatT) (uvars := 0) (Γ := []) (c := ``Nat.succ)
    (ci := ⟨0, .forallE (.const ``Nat []) (.const ``Nat [])⟩) (ls := []) (ls' := [])
    envNatT_succ (by simp) (by simp) (by simp) (by simp)

theorem envNatT_towerType : ∀ n : Nat, envNatT.HasType 0 [] (vNatTower n) (.const ``Nat [])
  | 0 => envNatT_zeroType
  | n + 1 =>
      -- `B.inst a` is `(.const Nat []).inst _`, i.e. `.const Nat []` by iota.
      VEnv.IsDefEq.appDF envNatT_succType (envNatT_towerType n)

/-- **The literal translates** — the witness the bridge's `hex` premise asks for, at every
`n`, constructed (not assumed). It is `TrExprS.lit` all the way down: lean4lean translates
`.lit l` *through* `Literal.toConstructor`, which under peano is the very unfolding the
shipping `visitLiteral` performs. -/
theorem trExprS_natLit : ∀ n : Nat, TrExprS envNatT [] [] (.lit (.natVal n)) (vNatTower n)
  | 0 => .lit (envNatT_containsLits 0) (.const envNatT_zero (by simp) (by simp))
  | n + 1 => .lit (envNatT_containsLits (n + 1))
      (.app envNatT_succType (envNatT_towerType n)
        (.const envNatT_succ (by simp) (by simp)) (trExprS_natLit n))

/-! ### Non-vacuity guards for `Erases.const_fix` and the re-founded `Erases.fix`

The re-founded rule is easy to render *vacuous*: `hreg` needs a `Γ` that really
registers the block, and `hsrc` + `hbodies` pin the conclusion's source `.lam` to the
`idx`-th body, which must erase to that def's **unfolding**. Everything below is
constructed at a concrete `Γ` — nothing is assumed — and the block is genuinely
recursive: it is `def f (a : Prop) := f a`, whose erasure is

    fixRecDefs = [ f ↦ λa. #1 #0 ]     (the fix binder is `#1` under the λ)
    fixRecSrc  = fun (a : Prop) => f a

so the sole def's unfolding is `λa. (fix f. λa. f a) #0` and the self-reference inside
it is discharged by the `const_fix` leaf. This is exactly the shape `visitMutual` emits
(`mkDef` closes the sibling fvar to `.bvar 1`), and it is *not* the pre-W1 fixture: the
old rule related a **dummy** source `.lam` to the contentless self-loop `fix f. f`,
which is what made it — and, with it, the `NoFix`-free forward simulation — unsound
(the record is `EnvErasureRec`'s Part 3b). -/

/-- The emitted block for `def f (a : Prop) := f a`: one def, whose body is the closed
`λa. #1 #0` (`#1` = the fix binder, `#0` = `a`). `principalArgIdx` is the `Basic.lean`
default `0`, as `mkDef` always leaves it. -/
def fixRecDefs : List (@FixDef LBTerm) :=
  [{ name := .named "f", body := .lambda (nameToBinder `a) (.app (.bvar 1) (.bvar 0)) }]

/-- The source body of that def: `fun (a : Prop) => f a`. -/
def fixRecSrc : Expr := .lam `a (.sort .zero) (.app (.const `f []) (.bvar 0)) .default

/-- A concrete `Γ` registering the one-def block above under the name `f`. -/
def ΓfixRec : ErasureCtx where
  inductives := fun _ => none
  constants := toKername
  recBodies := fun n => if n = `f then some (fixRecDefs, 0) else none

theorem ΓfixRec_recBodies : ΓfixRec.recBodies `f = some (fixRecDefs, 0) := by
  simp [ΓfixRec]

/-- The block is inert under every de Bruijn operation (it is closed and fvar-free),
which is what the three LBTerm-side premises of `const_fix`/`fix` record. -/
theorem fixRecDefs_shift (d c : Nat) :
    LBTerm.shift d c (.fix fixRecDefs 0) = .fix fixRecDefs 0 := by
  simp only [fixRecDefs, LBTerm.shift, LBTerm.shiftDefs, List.length_cons, List.length_nil]
  rw [if_neg (by omega), if_neg (by omega)]

theorem fixRecDefs_subst (s : LBTerm) (d : Nat) :
    LBTerm.subst s d (.fix fixRecDefs 0) = .fix fixRecDefs 0 := by
  simp only [fixRecDefs, LBTerm.subst, LBTerm.substDefs, List.length_cons, List.length_nil]
  rw [if_pos (by omega), if_pos (by omega)]

theorem fixRecDefs_toBvar (x : FVarId) (l : Nat) :
    toBvar x l (.fix fixRecDefs 0) = .fix fixRecDefs 0 := rfl

/-- **Non-vacuity (`Erases.const_fix`)**: the registered recursive constant `f` relates
to its own block. (At the default `Γ` — `recBodies = fun _ => none` — the rule is
refuted by `simp`, so the registration is doing the work.) -/
theorem erases_const_fixRec (env : VEnv) (Us : List Name) (Δ : VLCtx) (us : List Level) :
    Erases env Us ΓfixRec Δ (.const `f us) (.fix fixRecDefs 0) :=
  .const_fix `f us ΓfixRec_recBodies (by simp [ΓfixRec]) (by simp [ΓfixRec])
    fixRecDefs_shift fixRecDefs_subst fixRecDefs_toBvar

/-- The one-step unfolding of the block's sole def, computed: the fix binder is replaced
by the block itself, so the recursive call becomes `.fix fixRecDefs 0` applied to `#0`. -/
theorem fixRecDefs_unfold :
    LBTerm.substList (LBTerm.fixSubst fixRecDefs) (fixRecDefs[0]'(by simp [fixRecDefs])).body
      = .lambda (nameToBinder `a) (.app (.fix fixRecDefs 0) (.bvar 0)) := rfl

/-- **Non-vacuity (`Erases.fix`, re-founded)**: `fun (a : Prop) => f a` erases to
`fix f. λa. f a` at the registering `Γ`, at any `Δ`. The `hbodies` premise is discharged
*through* the `const_fix` leaf — which is what makes the (genuinely self-referential)
premise finite. -/
theorem erases_fixRec (env : VEnv) (Us : List Name) (Δ : VLCtx) :
    Erases env Us ΓfixRec Δ fixRecSrc (.fix fixRecDefs 0) := by
  refine .fix 0 (nms := [`f]) (srcs := [fixRecSrc]) Nat.zero_lt_one rfl rfl rfl
    (fun j h => ?_) (fun d hd => ?_)
    (fun s d => rfl) (fun e₀ d => rfl) (fun v d => rfl)
    fixRecDefs_shift fixRecDefs_subst fixRecDefs_toBvar (fun j h Δf => ?_)
  · -- `hreg`: the block is registered under its own (sole) name
    obtain rfl : j = 0 := by simp only [fixRecDefs, List.length_cons, List.length_nil] at h; omega
    exact ΓfixRec_recBodies
  · -- `hrarg`: `mkDef` leaves the principal argument index at the default `0`
    simp only [fixRecDefs, List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd; rfl
  · -- `hbodies`: the body erases to the def's unfolding, the recursive call by `const_fix`
    obtain rfl : j = 0 := by simp only [fixRecDefs, List.length_cons, List.length_nil] at h; omega
    rw [fixRecDefs_unfold]
    exact .lam (ty' := .sort .zero) (.sort rfl)
      (.app (erases_const_fixRec env Us _ []) (.bvar 0))

/-! ### Non-vacuity guards for `Erases.fixvar` (W3.1)

The fixvar leaf is the *other half* of the same fixture: while `visitMutual` is erasing
the block, the reader carries `fixvars := {f ↦ x}` (`Erasure.lean`'s `withReader`), and a
reference to the sibling `f` comes out as `.fvar x` rather than `.const (toKername f)`.
`mkDef`/`closeFix` then binds `x` to `.bvar 1`, which is exactly `fixRecDefs`' body — so
the two guards below and `erases_fixRec` above describe the same run at its two stages. -/

/-- The **block-local** `Γ`: `ΓfixRec` plus the fixvar map the run installs while erasing
the block (`Erasure.lean`'s `withReader … fixvars`). Top-level `Γ`s keep the field's
`fun _ => none` default, which is the forward simulations' `hnfv`. -/
def ΓfixOpen (x : FVarId) : ErasureCtx where
  inductives := fun _ => none
  constants := toKername
  recBodies := fun n => if n = `f then some (fixRecDefs, 0) else none
  fixvars := fun n => if n = `f then some x else none

/-- **Non-vacuity (`Erases.fixvar`)**: inside the block, the sibling reference `f` erases
to the fresh fvar the run minted for it — at every context that does not already bind
that fvar, which is every context the run builds (it mints `x` *before* opening any
binder). -/
theorem erases_fixvar_fixOpen (env : VEnv) (Us : List Name) (x : FVarId) (us : List Level)
    (Δ : VLCtx) (hx : x ∉ Δ.fvars) :
    Erases env Us (ΓfixOpen x) Δ (.const `f us) (.fvar x) :=
  .fixvar `f us x (by simp [ΓfixOpen]) (by simp [ΓfixOpen]) (by simp [ΓfixOpen]) hx

/-! ### Non-vacuity guards for `Erases.cases`

The three arity pins (`hpre`/`hnfs`+`hnlen`/`harity`) are easy to render *vacuous*:
both new `ErasureCtx` fields default to `fun _ => none`, which refutes `hpre` and
`hnfs` outright, so at the default `Γ` the rule is now unusable. Two constructed
witnesses, at concrete `Γ`s that do register the data:

* `Γcases0` — the degenerate shape: no parameters, no indices (`discrPos = 1`, the
  motive), one constructor with no fields, so the sole alternative has the empty
  telescope (`mkLambdas [] t = t`);
* `Γcases2` — the non-degenerate shape: **one parameter and one index**
  (`discrPos = 1 + 1 + 1 = 3`, so `pre` is strictly longer than the parameter list and
  the `hpre` pin is doing real work), **two** constructors with **one and two** fields,
  so `harity` is checked at two distinct non-zero telescopes and the minors erase
  through the `lam` rule (with real `TrExprS` side premises) rather than degenerately.
-/

/-- A concrete `Γ` registering `con` as `I.casesOn`: zero parameters, `discrPos = 1`
(motive only), one constructor with zero fields. -/
private def Γcases0 : ErasureCtx where
  inductives := fun _ => none
  constants := toKername
  casesOns := fun n => if n = `con then some (⟨toKername `I, 0⟩, 0) else none
  ctorFields := fun _ => some [0]
  casesDiscrPos := fun n => if n = `con then some 1 else none

/-- Non-vacuity (degenerate): `con motive d m` erases to `.case (iid, 0) ⟦d⟧ [([], ⟦m⟧)]`.
`pre`'s single element is unconstrained — the rule imposes no erasure on the dropped
prefix, only its length. -/
example (env : VEnv) (Us : List Name) (Δ : VLCtx) (x y : FVarId) :
    Erases env Us Γcases0 Δ
      ((((Expr.const `con []).app (.sort .zero)).app (.fvar x)).app (.fvar y))
      (.case (⟨toKername `I, 0⟩, 0) (.fvar x) [([], .fvar y)]) := by
  refine .cases `con [] ⟨toKername `I, 0⟩ 0 [.sort .zero]
    (by simp [Γcases0]) (by simp [Γcases0]) rfl (.fvar x)
    (minors := [.fvar y]) (nfs := [0]) rfl rfl (fun j h => ?_) (fun j h => ?_)
  · obtain rfl : j = 0 := by simp only [List.length_cons, List.length_nil] at h; omega
    rfl
  · obtain rfl : j = 0 := by simp only [List.length_cons, List.length_nil] at h; omega
    exact .fvar y

/-- A concrete `Γ` registering `con` as `J.casesOn`: **one** parameter, one index
(hence `discrPos = 3`), and **two** constructors, with one and two fields. -/
private def Γcases2 : ErasureCtx where
  inductives := fun _ => none
  constants := toKername
  casesOns := fun n => if n = `con then some (⟨toKername `J, 0⟩, 1) else none
  ctorFields := fun _ => some [1, 2]
  casesDiscrPos := fun n => if n = `con then some 3 else none

/-- Non-vacuity (non-degenerate): `con param motive index d m₁ m₂` with
`m₁ = fun a => a` and `m₂ = fun a b => a` erases to
`.case (iid, 1) ⟦d⟧ [([a], .bvar 0), ([a, b], .bvar 1)]` — two alternatives with
distinct, non-empty telescopes matching `ctorFields = [1, 2]`, and a three-element
dropped prefix matching `casesDiscrPos = 3`. -/
example (env : VEnv) (Us : List Name) (Δ : VLCtx) (x : FVarId) (a b : Name) :
    Erases env Us Γcases2 Δ
      ([Expr.fvar x,
        .lam a (.sort .zero) (.bvar 0) .default,
        .lam a (.sort .zero) (.lam b (.sort .zero) (.bvar 1) .default) .default].foldl
          Expr.app
        ([Expr.sort .zero, .sort .zero, .sort .zero].foldl Expr.app (.const `con [])))
      (.case (⟨toKername `J, 0⟩, 1) (.fvar x)
        [([nameToBinder a], .bvar 0), ([nameToBinder a, nameToBinder b], .bvar 1)]) := by
  refine .cases `con [] ⟨toKername `J, 0⟩ 1 [.sort .zero, .sort .zero, .sort .zero]
    (by simp [Γcases2]) (by simp [Γcases2]) rfl (.fvar x)
    (nfs := [1, 2]) rfl rfl (fun j h => ?_) (fun j h => ?_)
  · match j, h with
    | 0, _ => rfl
    | 1, _ => rfl
  · match j, h with
    | 0, _ => exact .lam (ty' := .sort .zero) (.sort rfl) (.bvar 0)
    | 1, _ =>
        exact .lam (ty' := .sort .zero) (.sort rfl)
          (.lam (ty' := .sort .zero) (.sort rfl) (.bvar 1))

end LeanToLambdaBox
