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

* **Projection-free.** `.proj`/`LBTerm.proj` are excluded *because lean4lean's
  projection translation `TrProj` and `inferProj.WF` are `sorry`* — see memory
  `lean4lean-sorry-boundary`. Including them would make every downstream result
  rest on lean4lean sorries.
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
`box | bvar | fvar | const | app | lam | letE | ctor | cases` (`fix` next).

## Trust boundary: inherited `sorryAx`

lean4lean's reusable `TrExprS` structural lemmas (`weakBV`, `inst`, `instN`, …) are
monolithic inductions over *all* `Expr` constructors; their `proj` case calls
lean4lean's sorried `TrProj`. So those lemmas carry `sorryAx`, and every result
here that uses them (`erases_shift`, `erases_subst`, …) inherits `sorryAx` — *even
on projection-free terms*. This is intentional and in scope: lean4lean's job is to
prove the Lean kernel correct; ours is to prove the transpilation pipeline correct
**assuming** that. lean4lean's results — including its still-open projection
metatheory — are used as-is as assumed building blocks. The `sorryAx` reported by
`#print axioms` is exactly the trust boundary "modulo the Lean kernel's correctness
as formalized by lean4lean"; we do not try to eliminate it. See memory
`lean4lean-sorry-boundary`.
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

`LBTerm.shiftArgs`/`shiftAlts` (and their `subst` counterparts) are hand-rolled
traversals (the structural-recursion checker cannot see through `List.map` for a nested
inductive). These four lemmas expose them as maps, which is what every `LBTerm.recData`
induction below needs in its `hconstruct`/`hcase` arm. Stated here (rather than after
`mkLambdas`, where they used to live) because `noFix_shift`/`noFix_subst` now have a
`.case` arm. -/

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

/-! ### `NoFix`: fix-free target terms

`NoFix t` holds when `t` contains no `.fix` node in relevant (spine) position. The
shipping `visitExpr` **never** emits `.fix` (only the environment-level `visitMutual`
does — P3), so every `visitExpr` output is `NoFix`. It is threaded through the
forward-simulation theorems purely to discharge the (vacuous, in that fragment) `.fix`
disjunct that `Erases.lam_inv` gains once `Erases.fix` is added: a `.lam`-source that
erases via the fix rule has target `.fix …`, and `NoFix (.fix …)` is `False`.

`.construct`/`.proj` are opaque (`True`): the data fragment's applied-form
constructor spines carry their arguments through `.app` (`mkApps (.construct … []) args`),
so `NoFix` reaches them via the `.app` recursion, not the (always-empty) `.construct`
node.

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
  | .proj _ _ => True
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
@[simp] theorem NoFix_proj (p : ProjectionInfo) (e : LBTerm) : NoFix (.proj p e) := trivial
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
  /-- **Environment-level mutual `fix` (P3, `notes/P3_ENV_ERASURE_DESIGN.md` §1).**
      Lean has no fixpoint node — recursion is created at the environment level by
      `visitMutual` (Erasure.lean:904), which erases each recursive def body with its
      sibling `.const`s mapped to fresh fvars `ids`, closes the result with `mkDef`
      (`closeFix`), and emits a `.fix defs j` decl per name. This rule reconstructs
      that: the source is the (syntactically `.lam`-headed) recursive body
      `.lam n ty b bi` of the `idx`-th def; `osrcs`/`obodies` are the block's opened
      (fvar-siblinged) source bodies and target bodies; `hbodies` relates them (in
      fvar-open form, at the fixed erasure context `Δf`); `hclose` ties each closed
      `defs[j].body` back to its opened form via `closeFix` (`FixMetatheory`).

      Design (Option B — the fixvar reconciliation is confined to the rule's premises,
      not a global `.const→.fvar` leaf rule, so `const_inv` is untouched): the source
      is a syntactic `.lam`, which confines the inversion ripple to `lam_inv` alone
      (every other inversion's catch-all refutes a `.lam`-headed source by head
      mismatch). The block is **closed** (top-level recursive defs are closed,
      fvar-free terms): the `hlift`/`hinst`/`habsl`/`hshift`/`hsubst`/`htobv`
      transport-inertness equalities record exactly that (each de-Bruijn op is the
      identity on the source `.lam` / target `.fix`), which is what makes the transport
      metatheory (`erases_shift`/`erases_subst`/`Erases.abstract`/`thin_vlet`) reuse
      the fix fields verbatim — no `fixExtend` cutoff bookkeeping needed (cf. §7). -/
  | fix {Δ : VLCtx} (idx : Nat)
      {Δf : VLCtx}
      {n : Name} {ty b : Expr} {bi : BinderInfo}
      {ids : List FVarId}
      {osrcs : List Expr} {obodies : List LBTerm}
      {defs : List (@FixDef LBTerm)}
      (hidx : idx < defs.length)
      (holen : osrcs.length = defs.length)
      (hblen : obodies.length = defs.length)
      (hilen : ids.length = defs.length)
      (hlift : ∀ (s d : Nat), (Expr.lam n ty b bi).liftLooseBVars' s d = .lam n ty b bi)
      (hinst : ∀ (e₀ : Expr) (d : Nat), (Expr.lam n ty b bi).instantiate1' e₀ d = .lam n ty b bi)
      (habsl : ∀ (v : FVarId) (d : Nat), (Expr.lam n ty b bi).abstract1 v d = .lam n ty b bi)
      (hshift : ∀ (d c : Nat), LBTerm.shift d c (.fix defs idx) = .fix defs idx)
      (hsubst : ∀ (s : LBTerm) (d : Nat), LBTerm.subst s d (.fix defs idx) = .fix defs idx)
      (htobv : ∀ (x : FVarId) (l : Nat), toBvar x l (.fix defs idx) = .fix defs idx)
      (hclose : ∀ j (h : j < defs.length),
          (defs[j]'h).body = closeFix ids 0 (obodies[j]'(hblen ▸ h)))
      (hbodies : ∀ j (h : j < defs.length),
          Erases env Us Γ Δf (osrcs[j]'(holen ▸ h)) (obodies[j]'(hblen ▸ h))) :
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
  | @fix Δc idx Δf nm tty tb tbi ids osrcs obodies defs hidx holen hblen hilen
      hlift hinst habsl hshift hsubst htobv hclose hbodies _ihb =>
      -- The fix source/target are closed & fvar-free (top-level rec def): both de
      -- Bruijn ops are the identity (the inertness premises), so the fix fields
      -- transport verbatim (no `fixExtend` cutoff bookkeeping — cf. design §7).
      rw [hlift dk dn, hshift dn dk]
      exact .fix idx hidx holen hblen hilen hlift hinst habsl hshift hsubst htobv hclose hbodies

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
  | @fix Δc idx Δf nm tty tb tbi ids osrcs obodies defs hidx holen hblen hilen
      hlift hinst habsl hshift hsubst htobv hclose hbodies _ihb =>
      rw [hinst e₀ dk, hsubst s' dk]
      exact .fix idx hidx holen hblen hilen hlift hinst habsl hshift hsubst htobv hclose hbodies

/-! ### Non-vacuity guard for `Erases.fix`

A concrete 1-def block `def f := f` (the self-loop is out of scope for the *shipping*
recursion, but exercises the closing at the pure-`LBTerm` level): the sole def body is
the fix binder itself, opened to a fresh fvar `x` and re-closed to `.bvar 0` by
`closeFix`. The source is a dummy closed, fvar-free `.lam` (its exact shape is
irrelevant — the fix rule requires no `TrExprS` of the source, only the transport-
inertness equalities, which hold by `rfl`/computation for closed fvar-free terms).
Constructible against any `env`/`Us`/`Γ`/`Δ`/`Δf` — so the rule is non-vacuous. -/
example (env : VEnv) (Us : List Name) (Γ : ErasureCtx) (Δ Δf : VLCtx) :
    Erases env Us Γ Δ (.lam `a (.sort .zero) (.sort .zero) .default)
      (.fix [{ name := .named "f", body := .bvar 0 }] 0) := by
  refine .fix (Δf := Δf) 0 (ids := [⟨`x⟩]) (osrcs := [.fvar ⟨`x⟩]) (obodies := [.fvar ⟨`x⟩])
    (Nat.zero_lt_one) rfl rfl rfl
    (fun s d => rfl) (fun e₀ d => rfl) (fun v d => rfl)
    (fun d c => ?_) (fun s d => ?_) (fun x l => rfl)
    (fun j h => ?_) (fun j h => ?_)
  · -- shift is the identity: the sole body `.bvar 0` is below the (single) fix binder
    simp only [LBTerm.shift, LBTerm.shiftDefs, List.length_cons, List.length_nil]
    rw [if_neg (by omega)]
  · -- subst is the identity likewise
    simp only [LBTerm.subst, LBTerm.substDefs, List.length_cons, List.length_nil]
    rw [if_pos (by omega)]
  · -- closeFix [x] 0 (.fvar x) = .bvar 0  (the self-reference re-closes)
    obtain rfl : j = 0 := by simp only [List.length_cons, List.length_nil] at h; omega
    show (LBTerm.bvar 0) = closeFix [⟨`x⟩] 0 (.fvar ⟨`x⟩)
    exact (closeFixFold_fvar_head ⟨`x⟩ 0 []).symm
  · -- each opened body erases: `.fvar x ↦ .fvar x`
    obtain rfl : j = 0 := by simp only [List.length_cons, List.length_nil] at h; omega
    exact .fvar ⟨`x⟩

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
