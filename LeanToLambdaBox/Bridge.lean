import LeanToLambdaBox.Erases
import LeanToLambdaBox.ErasesAbstract
import LeanToLambdaBox.ErasesStrengthen
import Lean4Lean.Verify.LocalContext

/-!
# The `visitExpr` → `Erases` bridge, part 1: the supported fragment

Plan of record for connecting the **shipping** erasure (`Erasure.visitExpr`, now a
`partial_fixpoint` family — Task A) to the verified layer:

    visitExpr ──(fixpoint induction, this bridge)──▶ Erases ──(erases_correct)──▶ Eval

(The former plan — bridging through the pure de-Bruijn `eraseCore` — is
**impossible**: no context-free oracle `orc : Expr → Bool` can reproduce the
shipping oracle's context-dependent boxing; see the 2026-07-07 addendum in
`EraseCore.lean`'s feasibility probe. `eraseCore` remains as the pure
specification model.)

This file defines the **v1 supported fragment**: the syntactic class of source
terms on which the bridge theorem speaks. It deliberately covers
`bvar | fvar | const | app | lam | letE` and excludes:

* **constructor heads** (`Γ.ctors`) — *lifted since A8*: the shipping emits the
  *applied* form `.construct iid cidx []` under an application spine, while
  `Erases.ctor` is the args-inside *block* form, so bridging them needed an
  applied-form rule (`Erases.ctor_head`) and a simulation under `construct_app`
  semantics (`erases_correct_data`). Both landed; `ctorApp` below is the rule;
* **`mdata`** (`Erases` has no rule for it);
* **`String` literals** (the shipping `visitLiteral` `panic!`s) and **machine-`Nat`
  literals** (they route into `prim`, out of `Erases` by design);
* everything `visitExpr` itself panics on (`sort`, `forallE`, `mvar`).

Four rules extend it: `ctorApp` (saturated constructor applications, the data
fragment), `casesApp` (saturated `casesOn` applications with *manifest* λ minors, the ι
fragment), `natLit` (`Nat` literals at a `Γ` that declares peano mode) and `proj`
(structure projections at a `Γ` that registers the structure — the typeclass-dispatch
fragment, slice P8, whose bridge side is `ProjBridgeHyps` + motive 10). All four are
documented at their constructors, and all four are *registration-gated*: at the default
`Γ` each is unusable, which is what the paired guards below check.

`bvar` *is* in the fragment even though `visitExpr`'s `.bvar` case is
`unreachable!` on the locally-closed terms it actually visits: the predicate is
purely syntactic and must be closed under going below binders; recursion always
instantiates the binder with a fresh fvar first (`Supported.instantiate1'`).
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- `e` is a **manifest** λ-telescope of depth at least `n`.

Needed by the ι fragment: `Erasure.lambdaOrIntroToArity`'s "intro" branch
η-expands a non-`.lam` minor (`k (.app e (.fvar x)) …`), and `Erases` has **no η
rule** — no derivation relates a non-`.lam` source to a `.lambda`-headed target.
So only manifest lambdas keep the eraser inside the relation; see the
`Supported.casesApp` docstring for the coverage consequence. -/
def IsLamTelescope : Nat → Expr → Prop
  | 0,   _            => True
  | n+1, .lam _ _ b _ => IsLamTelescope n b
  | _+1, _            => False

@[simp] theorem IsLamTelescope_zero (e : Expr) : IsLamTelescope 0 e := trivial

/-- Manifest λ-telescopes survive opening a binder (both sides descend at the
same de Bruijn depth). -/
theorem IsLamTelescope.instantiate1' {n : Nat} {e v : Expr} :
    IsLamTelescope n e → ∀ k, IsLamTelescope n (e.instantiate1' v k) := by
  induction n generalizing e with
  | zero => intro _ _; trivial
  | succ n ih =>
    match e with
    | .lam nm ty b bi =>
      intro h k
      show IsLamTelescope (n + 1) (Expr.lam nm _ (b.instantiate1' v (k + 1)) bi)
      exact ih h (k + 1)
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .app _ _ | .letE _ _ _ _ _
    | .lit _ | .mdata _ _ | .proj _ _ _ | .forallE _ _ _ _ => intro h _; exact absurd h id

/-- A nonempty `foldl Expr.app` spine is an `.app` node. Used to refute the
spine-shaped `Supported` rules (`ctorApp`, `casesApp`) against
`.const`/`.lam`/`.letE`-headed goals. -/
theorem exists_app_of_foldl_app_ne_nil (f : Expr) :
    ∀ {args : List Expr}, args ≠ [] → ∃ g a, args.foldl Expr.app f = .app g a := by
  intro args h
  rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
  · exact absurd rfl h
  · exact ⟨init.foldl Expr.app f, last, by rw [List.concat_eq_append, List.foldl_append]; rfl⟩

/-- The v1 supported fragment of the `visitExpr`→`Erases` bridge (see module
docstring). Syntactic in the source term and the static erasure context `Γ`:
constants must be plain constants (not registered constructors / `casesOn`s) and
must belong to `known` — an abstract name class naming the **δ fragment**: the
constants the erased program may reference. Until slice D4a `known` scoped a
state-agreement field of `BridgeInv` ("every `known` constant is pre-registered in
the `ErasureState` with its `Γ` kername"), which is false at a cold start; what
scopes it now is `DeltaHyps` (`DeltaHyps.lean`), the run-keyed scope-side half of
that contract. -/
inductive Supported (known : Name → Prop) (Γ : ErasureCtx) : Expr → Prop
  | bvar (i : Nat) : Supported known Γ (.bvar i)
  | fvar (x : FVarId) : Supported known Γ (.fvar x)
  /-- A plain constant. Two ways to be usable (recursion wall, W3.1): it is already
      *registered* (`known`, so `get_constant_kername` hits and `Erases.const` fires), or
      it is an **in-block sibling** of the mutual block currently being erased
      (`Γ.fixvars n ≠ none`, so `visitConst` returns the block's fresh fvar and
      `Erases.fixvar` fires). A sibling need *not* be `known`: `visitMutual` registers the
      block only after erasing every body. -/
  | const (n : Name) (us : List Level) (hk : known n ∨ Γ.fixvars n ≠ none)
      (hctor : Γ.ctors n = none) (hcases : Γ.casesOns n = none) :
      Supported known Γ (.const n us)
  | app {f a : Expr} (hf : Supported known Γ f) (ha : Supported known Γ a) :
      Supported known Γ (.app f a)
  | lam {b : Expr} (n : Name) (ty : Expr) (bi : BinderInfo)
      (hb : Supported known Γ b) : Supported known Γ (.lam n ty b bi)
  | letE {v b : Expr} (n : Name) (ty : Expr) (nd : Bool)
      (hv : Supported known Γ v) (hb : Supported known Γ b) :
      Supported known Γ (.letE n ty v b nd)
  /-- A **`Nat` literal under `nat := .peano`** (Nat-literals wall, L3). `visitExpr`
      routes `.lit l` to `visitLiteral`, which under peano rebuilds the constructor tower
      one `visitConstructor` at a time — exactly the one-step unfolding
      `Literal.toConstructor` that lean4lean's `TrExprS.lit` and `Erases.lit` use. So `Γ`
      must register `Nat`'s two constructors at their real kernel indices
      (`Nat.zero ↦ 0`, `Nat.succ ↦ 1`) and `Γ.natPeano` must pin the mode, which the
      bridge cashes in against the run's own `(← read).config.nat` via
      `VisitExprRefines.BridgeInv.natcfg`.

      No `ctorArities`/`casesOns` premises: the literal path calls `visitConstructor`
      **directly**, bypassing `visitCtorEta` (where saturation lives) and `visitConstApp`
      (where `Γ.casesOns` is consulted) — compare motive 3's premise list, which asks only
      for `Γ.ctors cn`.

      `.strVal` is deliberately **out** at every `Γ`: the shipping `visitLiteral`
      `panic!`s on it, returning the `Inhabited` default, i.e. silently wrong output.
      Machine mode is out too — `.prim` has no `Erases` rule — and stays out because at
      `Γ.natPeano = false` this rule is unusable. -/
  | natLit (n : Nat) {iid : InductiveId}
      (hpeano : Γ.natPeano = true)
      (hzero : Γ.ctors ``Nat.zero = some (iid, 0))
      (hsucc : Γ.ctors ``Nat.succ = some (iid, 1)) :
      Supported known Γ (.lit (.natVal n))
  /-- A **structure projection** (projection round, slice P8) — the typeclass-dispatch
      fragment. `visitExpr` routes `.proj S i d` to `visitProj`, which looks `S` up,
      registers it, and emits `.proj ⟨iid, np, i⟩` over the erased discriminant. The three
      `Γ` premises are `Erases.proj`'s, verbatim, so a supported projection is one the
      bridge can actually match:

      * `hs` — `S` is a registered **structure** with `np` parameters (`Γ.projs`), which is
        what `ProjBridgeHyps.projind_run`/`projreg_run` cash in against the run;
      * `hnfs` — its inductive has exactly one constructor, with `nf` retained fields,
        which is `register_inductive`'s own `is_struct` gate and what makes both the target
        rule's hard-wired constructor index `0` and the *single* argmask correct;
      * `hi` — the field index is in range, which is also what makes the eraser's
        post-argmask `fieldIdx` equal `i` (`count_keep_take_replicate`).

      The discriminant must itself be supported. **Nothing is asked of `S`'s
      declaration**: `visitProj`'s `getConstInfo`/`register_inductive` never fail on a
      registered structure, which is exactly what `ProjBridgeHyps` asserts.

      Unusable at a `Γ` that registers no structure (`Γ.projs = fun _ => none`), like every
      other registration-gated rule — the guards below check both polarities. -/
  | proj {S : Name} {i : Nat} {d : Expr} {iid : InductiveId} {np nf : Nat}
      (hs : Γ.projs S = some (iid, np))
      (hnfs : Γ.ctorFields iid = some [nf])
      (hi : i < nf)
      (hd : Supported known Γ d) :
      Supported known Γ (.proj S i d)
  /-- A **saturated constructor application** (data-fragment extension, A8). The
      head `cn` is a registered constructor (`Γ.ctors`) with declared arity `ar`
      (`Γ.ctorArities`); the spine is exactly saturated (`args.length = ar`), so the
      shipping `visitCtorEta` takes the `visitConstructor` branch (no η-expansion),
      and — being neither `Nat.zero` nor `Nat.succ` — the machine-`Nat` special-casing
      of `visitConstructor` is dead. Every argument is itself supported. -/
  | ctorApp {cn : Name} {us : List Level} {iid : InductiveId} {cidx ar : Nat}
      {args : List Expr}
      (hc : Γ.ctors cn = some (iid, cidx)) (hcases : Γ.casesOns cn = none)
      (har : Γ.ctorArities cn = some ar)
      (hsat : args.length = ar)
      (hzero : cn ≠ ``Nat.zero) (hsucc : cn ≠ ``Nat.succ)
      (hargs : ∀ i (hi : i < args.length), Supported known Γ (args[i])) :
      Supported known Γ (args.foldl Expr.app (.const cn us))
  /-- A **saturated `casesOn` application** (ι fragment, C4). Mirrors `ctorApp`'s
      saturation discipline. `con` is a registered `casesOn` head (`Γ.casesOns`) whose
      discriminant sits at `Γ.casesDiscrPos con = some dp`; the inductive has
      per-constructor field-count list `Γ.ctorFields iid = some nfs`; the spine is
      **exactly** `dp` dropped arguments, the discriminant, and one minor per
      constructor — i.e. `CasesInfo.arity` arguments — so `visitCasesEtaGo`'s
      η-expansion branch is dead. The dropped prefix `pre` (params/motive/indices)
      carries **no** obligation: `Erases.cases` imposes none, and the eraser never
      visits it. `con.getPrefix ∉ {Nat, Int}` kills `visitCases`' machine-`Nat`/`Int`
      special cases purely, exactly as `cn ≠ Nat.zero/succ` does for `ctorApp`.
      Over-application composes on top via `Supported.app`.

      **Fragment boundary** (deliberate, and forced by the model): each minor is a
      **manifest** λ-telescope of at least its constructor's field count (`hlam`) —
      the eraser's `lambdaOrIntroToArity` intro branch η-expands, which `Erases`
      cannot model (no η rule). Lean's `match` compiler emits minors as explicit
      `fun a b => …`, so real pattern-matching code is inside the fragment;
      hand-written η-contracted minors (`Option.casesOn o none Some`) are not.
      Fixing that needs an `Erases`-level η rule, not more proof effort.
      The conclusion is spelled with the *flat* spine `pre ++ discr :: minors`;
      `List.foldl_append` relates it to `Erases.cases`' nested
      `(discr :: minors).foldl _ (pre.foldl _ _)`. -/
  | casesApp {con : Name} {us : List Level} {iid : InductiveId} {np dp : Nat}
      {nfs : List Nat} {pre minors : List Expr} {discr : Expr}
      (hc : Γ.casesOns con = some (iid, np))
      (hdp : Γ.casesDiscrPos con = some dp)
      (hnfs : Γ.ctorFields iid = some nfs)
      (hpre : pre.length = dp)
      (hsat : minors.length = nfs.length)
      (hnat : con.getPrefix ≠ ``Nat) (hint : con.getPrefix ≠ ``Int)
      (hdiscr : Supported known Γ discr)
      (hlam : ∀ j (h : j < minors.length), IsLamTelescope (nfs[j]'(hsat ▸ h)) (minors[j]))
      (hminors : ∀ j (h : j < minors.length), Supported known Γ (minors[j])) :
      Supported known Γ ((pre ++ discr :: minors).foldl Expr.app (.const con us))

/-- The fragment is closed under opening a binder with a free variable — the
form in which the bridge's binder cases recurse (`lambdaMonocular`/`letMonocular`
call the continuation on `body.instantiate1 (.fvar x)`). -/
theorem Supported.instantiate1' {known : Name → Prop} {Γ : ErasureCtx} {e : Expr}
    (x : FVarId) (h : Supported known Γ e) :
    ∀ k, Supported known Γ (e.instantiate1' (.fvar x) k) := by
  induction h with intro k
  | bvar i =>
    simp only [Expr.instantiate1']
    split
    · exact .bvar _
    · split
      · exact .fvar x
      · exact .bvar _
  | fvar y => exact .fvar y
  | const n us hk hctor hcases => exact .const n us hk hctor hcases
  | app _ _ ihf iha => exact .app (ihf k) (iha k)
  | lam n ty bi _ ihb => exact .lam n _ bi (ihb (k + 1))
  | letE n ty nd _ _ ihv ihb => exact .letE n _ nd (ihv k) (ihb (k + 1))
  | natLit n hpeano hz hs => exact .natLit n hpeano hz hs
  | proj hs hnfs hi _ ihd => exact .proj hs hnfs hi (ihd k)
  | ctorApp hc hcases har hsat hzero hsucc _ ihargs =>
    rw [instantiate1'_foldl_app]
    simp only [Expr.instantiate1']
    refine .ctorApp hc hcases har (by simp [hsat]) hzero hsucc (fun i hi => ?_)
    rw [List.getElem_map]
    exact ihargs i (by simpa using hi) k
  | @casesApp con us iid np dp nfs pre minors discr hc hdp hnfs hpre hsat hnat hint
      hdiscr hlam hminors ihdiscr ihminors =>
    rw [instantiate1'_foldl_app]
    simp only [Expr.instantiate1', List.map_append, List.map_cons]
    refine .casesApp (pre := pre.map (·.instantiate1' (.fvar x) k))
      (minors := minors.map (·.instantiate1' (.fvar x) k))
      (discr := discr.instantiate1' (.fvar x) k)
      hc hdp hnfs (by simp [hpre]) (by simp [hsat]) hnat hint (ihdiscr k)
      (fun j hj => ?_) (fun j hj => ?_)
    · rw [List.getElem_map]
      exact (hlam j (by simpa using hj)).instantiate1' k
    · rw [List.getElem_map]
      exact ihminors j (by simpa using hj) k

/-- Version at the real `Expr.instantiate1` (what the shipping code runs),
transported along lean4lean's modeling axiom `instantiate1_eq`. -/
theorem Supported.instantiate1 {known : Name → Prop} {Γ : ErasureCtx} {e : Expr}
    (x : FVarId) (h : Supported known Γ e) :
    Supported known Γ (e.instantiate1 (.fvar x)) := by
  rw [Lean.Expr.instantiate1_eq]
  exact h.instantiate1' x 0

/-- **The fragment enters a mutual block** (recursion wall, slice Γ-W0). Every rule but
`const` reads only registration fields that `ErasureCtx.withFixvars` leaves alone, so the
whole derivation transports field-by-field. `const` is the one rule that reads `fixvars`,
through the disjunct `known n ∨ Γ.fixvars n ≠ none`; at an ambient `Γ` — where
`DeltaHyps.nofixvars` pins `Γ.fixvars = ⊥` — that disjunct's second half is *dead*, so
every `.const` node in the derivation carries `known n`, which transports to any `fv`.

The fragment therefore **grows**: at `Γ.withFixvars fv` the second disjunct becomes live
for the block's own siblings, which is what makes a sibling reference supported at
`known = ⊥` (`VisitExprRefines`' guard (i''), and the negative half
`supported_const_fixOpen_not_ambient`). The converse direction is *false* for exactly that
reason, which is why `hnfv` is a premise here rather than the statement being an iff. -/
theorem Supported.withFixvars {known : Name → Prop} {Γ : ErasureCtx} {e : Expr}
    (hnfv : Γ.fixvars = fun _ => none) (h : Supported known Γ e)
    (fv : Name → Option FVarId) : Supported known (Γ.withFixvars fv) e := by
  induction h with
  | bvar i => exact .bvar i
  | fvar x => exact .fvar x
  | const n us hk hctor hcases =>
    refine .const n us (.inl ?_) (by simpa using hctor) (by simpa using hcases)
    rcases hk with hk | hfx
    · exact hk
    · exact absurd (by rw [hnfv]) hfx
  | app _ _ ihf iha => exact .app ihf iha
  | lam n ty bi _ ihb => exact .lam n ty bi ihb
  | letE n ty nd _ _ ihv ihb => exact .letE n ty nd ihv ihb
  | natLit n hpeano hzero hsucc =>
    exact .natLit n (by simpa using hpeano) (by simpa using hzero) (by simpa using hsucc)
  | proj hs hnfs hi _ ihd =>
    exact .proj (by simpa using hs) (by simpa using hnfs) hi ihd
  | ctorApp hc hcases har hsat hzero hsucc _ ihargs =>
    exact .ctorApp (by simpa using hc) (by simpa using hcases) (by simpa using har)
      hsat hzero hsucc ihargs
  | casesApp hc hdp hnfs hpre hsat hnat hint _ hlam _ ihdiscr ihminors =>
    exact .casesApp (by simpa using hc) (by simpa using hdp) (by simpa using hnfs)
      hpre hsat hnat hint ihdiscr hlam ihminors

/-! Non-vacuity guards: the fragment is inhabited at every rule, and genuinely
excludes the unsupported constructs. -/

example : Supported (fun _ => True)
    ⟨fun _ => none, fun _ => ⟨.MPfile [], "x"⟩, fun _ => none, fun _ => none, fun _ => none,
      fun _ => none, fun _ => none, false, fun _ => none, fun _ => none, fun _ => none⟩
    (.lam `x (.const `Nat []) (.bvar 0) .default) :=
  .lam _ _ _ (.bvar 0)

/-- Literals are out of the fragment at a **machine-mode or unflagged** `Γ`: `natLit` is
gated on `Γ.natPeano = true`, so at `false` the exclusion the fragment always had is
intact — in particular the machine path (`.prim`, which has no `Erases` rule) is still
unreachable from `Supported`. -/
example {known : Name → Prop} {Γ : ErasureCtx} (hΓ : Γ.natPeano = false) :
    ¬ Supported known Γ (.lit (.natVal 0)) := by
  intro h
  generalize he : (Expr.lit (Literal.natVal 0)) = e at h
  cases h with
  | @ctorApp cn us iid cidx ar args hc hcases har hsat hz hs hargs =>
      rcases List.eq_nil_or_concat args with rfl | ⟨i, l, rfl⟩ <;>
        simp only [List.foldl_nil, List.concat_eq_append, List.foldl_append,
          List.foldl_cons, List.foldl_nil] at he <;> exact absurd he (by simp)
  | @casesApp con us iid np dp nfs pre minors discr hc hdp hnfs hpre hsat hnat hint
      hdiscr hlam hminors =>
      obtain ⟨g, a, hga⟩ := exists_app_of_foldl_app_ne_nil (Expr.const con us)
        (args := pre ++ discr :: minors) (by simp)
      rw [hga] at he; exact absurd he (by simp)
  | _ => simp_all

/-- A **`String` literal** is out, and stays out even once the peano-`Nat` rule lands:
the shipping `visitLiteral` `panic!`s on `.strVal` (returning the `Inhabited` default —
silently wrong output), so it must never be inside the fragment. -/
example {known : Name → Prop} {Γ : ErasureCtx} :
    ¬ Supported known Γ (.lit (.strVal "x")) := by
  intro h
  generalize he : (Expr.lit (Literal.strVal "x")) = e at h
  cases h with
  | @ctorApp cn us iid cidx ar args hc hcases har hsat hz hs hargs =>
      rcases List.eq_nil_or_concat args with rfl | ⟨i, l, rfl⟩ <;>
        simp only [List.foldl_nil, List.concat_eq_append, List.foldl_append,
          List.foldl_cons, List.foldl_nil] at he <;> exact absurd he (by simp)
  | @casesApp con us iid np dp nfs pre minors discr hc hdp hnfs hpre hsat hnat hint
      hdiscr hlam hminors =>
      obtain ⟨g, a, hga⟩ := exists_app_of_foldl_app_ne_nil (Expr.const con us)
        (args := pre ++ discr :: minors) (by simp)
      rw [hga] at he; exact absurd he (by simp)
  | _ => simp_all

/-- **`Supported.natLit` is inhabited** (the positive half of the pair above): at the
peano fixture `ΓnatLit` — the same `Γ` at which `erases_natLit` derives the tower
(`Erases.lean`) and `sevalData_natLit`/`wcbvEval_natLitTower` run it
(`ErasesCorrectData.lean`) — every `Nat` literal is in the fragment. So the bridge's
literal dispatch is not vacuously discharged. -/
example : Supported (fun _ => True) ΓnatLit (.lit (.natVal 3)) :=
  .natLit 3 (by simp [ΓnatLit]) ΓnatLit_zero ΓnatLit_succ

/-- **A projection is out of the fragment at a `Γ` that registers no structure** — the
negative half of the pair, and the same shape the `natLit` guard has: the rule exists, and
is *unusable* at the default context.

This is the P1-era exclusion, restated. It used to hold at **every** `Γ`, for a reason
that has now expired: `Supported.proj` did not exist, because step 1's `cases hsupp` is a
complete case analysis and only motive 10 could discharge a `proj` arm, and motive 10
concluded `True`. Slice P8 gave motive 10 content, the arm is discharged, and what is left
is the ordinary registration gate — `Γ.projs = ⊥` makes `hs` unsatisfiable. -/
example {known : Name → Prop} {Γ : ErasureCtx} (hnp : Γ.projs = fun _ => none) :
    ¬ Supported known Γ (.proj `Prod 0 (.fvar ⟨`p⟩)) := by
  intro h
  generalize he : (Expr.proj `Prod 0 (.fvar ⟨`p⟩)) = e at h
  cases h with
  | @proj S i d iid np nf hs hnfs hi hd => rw [hnp] at hs; exact absurd hs (by simp)
  | @ctorApp cn us iid cidx ar args hc hcases har hsat hz hs hargs =>
      rcases List.eq_nil_or_concat args with rfl | ⟨i, l, rfl⟩ <;>
        simp only [List.foldl_nil, List.concat_eq_append, List.foldl_append,
          List.foldl_cons, List.foldl_nil] at he <;> exact absurd he (by simp)
  | @casesApp con us iid np dp nfs pre minors discr hc hdp hnfs hpre hsat hnat hint
      hdiscr hlam hminors =>
      obtain ⟨g, a, hga⟩ := exists_app_of_foldl_app_ne_nil (Expr.const con us)
        (args := pre ++ discr :: minors) (by simp)
      rw [hga] at he; exact absurd he (by simp)
  | _ => simp_all

/-- **`Supported.proj` is inhabited** (the positive half of the pair above): at `Γproj` —
the one-parameter, one-field structure fixture at which `erases_proj_fvar`/`erases_proj_ctor`
derive the erasure (`Erases.lean`) and at which the target step fires
(`EnvErasureNonrec.lean`) — a projection of a variable is in the fragment. So the bridge's
projection dispatch is not vacuously discharged. -/
example (x : FVarId) : Supported (fun _ => True) Γproj (.proj `AC 0 (.fvar x)) :=
  .proj Γproj_projs Γproj_ctorFields (by omega) (.fvar x)

/-- **…and so is a projection of a saturated constructor spine**, the redex shape the
forward simulation runs on: the discriminant is `ctorApp` at the structure's own
constructor. The whole `.proj` node — not merely what is under it — is now inside the
fragment. -/
example (x y : FVarId) :
    Supported (fun _ => True) Γproj
      (.proj `AC 0 ([Expr.fvar x, .fvar y].foldl Expr.app (.const `AC.mk []))) :=
  .proj Γproj_projs Γproj_ctorFields (by omega)
    (.ctorApp (iid := projInd) (cidx := 0) (ar := 2) (args := [.fvar x, .fvar y])
      Γproj_ctors (by simp [Γproj]) Γproj_arity rfl (by decide) (by decide)
      (fun i hi => by
        match i, hi with
        | 0, _ => exact .fvar x
        | 1, _ => exact .fvar y))

/-- The discriminant side on its own, kept from the P1 era as the record of what the
projection round had before it had the node. -/
example (x y : FVarId) :
    Supported (fun _ => True) Γproj
      ([Expr.fvar x, .fvar y].foldl Expr.app (.const `AC.mk [])) :=
  .ctorApp (iid := projInd) (cidx := 0) (ar := 2) (args := [.fvar x, .fvar y])
    Γproj_ctors (by simp [Γproj]) Γproj_arity rfl (by decide) (by decide)
    (fun i hi => by
      match i, hi with
      | 0, _ => exact .fvar x
      | 1, _ => exact .fvar y)

/-- **The sibling alternative of `Supported.const` is inhabited** (recursion wall, W3.1):
inside a mutual block, a reference to the block's own name `f` is in the fragment even at
`known := ⊥` — it is *not* registered yet (`visitMutual` registers the block only after
erasing every body), and it must not have to be. `ΓfixOpen` is `Erases.lean`'s W1 fixture
at its open stage, i.e. exactly the reader `visitMutual` installs. -/
example (x : FVarId) (us : List Level) :
    Supported (fun _ => False) (ΓfixOpen x) (.const `f us) :=
  .const `f us (.inr (by simp [ΓfixOpen])) (by simp [ΓfixOpen]) (by simp [ΓfixOpen])

/-- A saturated nullary constructor *is* in the fragment (`ctorApp`, `args = []`,
`ar = 0`). -/
example (iid : InductiveId) :
    Supported (fun _ => True)
      ⟨fun _ => none, fun _ => ⟨.MPfile [], "x"⟩,
        fun n => if n = `c then some (iid, 0) else none,
        fun n => if n = `c then some 0 else none, fun _ => none,
        fun _ => none, fun _ => none, false, fun _ => none, fun _ => none, fun _ => none⟩
      (.const `c []) := by
  have h : (Expr.const `c []) = ([] : List Expr).foldl Expr.app (.const `c []) := rfl
  rw [h]
  refine .ctorApp (iid := iid) (cidx := 0) (ar := 0) (args := []) ?_ rfl ?_ rfl ?_ ?_ ?_
  · simp
  · simp
  · decide
  · decide
  · intro i hi; exact absurd hi (by simp)

/-- A saturated `casesOn` application *is* in the fragment (`casesApp`): `J` has
one parameter and one index, so the motive and the index push the discriminant to
`dp = 3 ≠ numParams`; the two constructors have **one and two** fields, so the
minors are genuine λ-telescopes of those depths. Exercises `hpre` at a `dp` that
is *not* the parameter count — the pin that stops an over-applied `casesOn` from
being re-parsed with the first minor as discriminant — and `hlam` at two distinct
non-zero telescope depths. -/
example (iid : InductiveId) (p m i d : FVarId) :
    Supported (fun _ => True)
      ⟨fun _ => none, fun _ => ⟨.MPfile [], "x"⟩, fun _ => none, fun _ => none,
        fun n => if n = `J.casesOn then some (iid, 1) else none,
        fun _ => some [1, 2],
        fun n => if n = `J.casesOn then some 3 else none, false,
        fun _ => none, fun _ => none, fun _ => none⟩
      ([Expr.fvar p, .fvar m, .fvar i, .fvar d,
          .lam `u (.const `U []) (.bvar 0) .default,
          .lam `u (.const `U []) (.lam `v (.const `V []) (.bvar 1) .default) .default].foldl
        Expr.app (.const `J.casesOn [])) := by
  have h : ([Expr.fvar p, .fvar m, .fvar i, .fvar d,
      .lam `u (.const `U []) (.bvar 0) .default,
      .lam `u (.const `U []) (.lam `v (.const `V []) (.bvar 1) .default) .default] : List Expr)
      = [Expr.fvar p, .fvar m, .fvar i] ++ Expr.fvar d ::
          [Expr.lam `u (.const `U []) (.bvar 0) .default,
           .lam `u (.const `U []) (.lam `v (.const `V []) (.bvar 1) .default) .default] := rfl
  rw [h]
  refine .casesApp (iid := iid) (np := 1) (dp := 3) (nfs := [1, 2]) (by simp) (by simp) rfl
    rfl rfl (by decide) (by decide) (.fvar d) ?_ ?_
  · intro j hj
    match j, hj with
    | 0, _ => exact (by trivial : IsLamTelescope 0 (Expr.bvar 0))
    | 1, _ => exact (by trivial : IsLamTelescope 0 (Expr.bvar 1))
  · intro j hj
    match j, hj with
    | 0, _ => exact .lam _ _ _ (.bvar 0)
    | 1, _ => exact .lam _ _ _ (.lam _ _ _ (.bvar 1))

/-! ## lctx ↔ `VLCtx` correspondence: extension lemmas

The bridge's induction invariant carries lean4lean's `TrLCtx env Us ctx.lctx Δ`
(the reader's `LocalContext` corresponds to the typing context `Δ`).
`Erasure.withLocalDecl`/`withLocalDef` extend the lctx with
`mkLocalDecl`/`mkLetDecl` (Erasure.lean:273/:278); these lemmas extend the
correspondence in lockstep. lean4lean has the ingredients
(`LocalContext.WF.mkLocalDecl`, `mkLocalDecl_toList`, `TrLCtx'.cons`) but not
the assembled statement. -/

theorem TrLCtx.mkLocalDecl {env : VEnv} {Us : List Name} {lctx : LocalContext}
    {Δ : VLCtx} {x : FVarId} {n : Name} {ty : Expr} {ty' : VExpr}
    {bi : BinderInfo}
    (H : TrLCtx env Us lctx Δ) (hx : lctx.find? x = none)
    (hty : TrExprS env Us Δ ty ty') (hty' : env.IsType Us.length Δ.toCtx ty') :
    TrLCtx env Us (lctx.mkLocalDecl x n ty bi)
      ((some (x, ty.fvarsList), .vlam ty') :: Δ) :=
  ⟨H.1.mkLocalDecl hx, by
    rw [LocalContext.mkLocalDecl_toList]
    exact H.2.cons (.vlam hty hty')⟩

theorem TrLCtx.mkLetDecl {env : VEnv} {Us : List Name} {lctx : LocalContext}
    {Δ : VLCtx} {x : FVarId} {n : Name} {ty val : Expr} {ty' val' : VExpr}
    {nd : Bool}
    (H : TrLCtx env Us lctx Δ) (hx : lctx.find? x = none)
    (hty : TrExprS env Us Δ ty ty') (hval : TrExprS env Us Δ val val')
    (hvt : env.HasType Us.length Δ.toCtx val' ty') :
    TrLCtx env Us (lctx.mkLetDecl x n ty val nd)
      ((some (x, ty.fvarsList ++ val.fvarsList), .vlet ty' val') :: Δ) :=
  ⟨H.1.mkLetDecl hx, by
    rw [LocalContext.mkLetDecl_toList]
    exact H.2.cons (.vlet hty hval hvt)⟩

/-! ## Looking up the freshly-bound declaration

`Erasure.fvar_to_name` (Erasure.lean:237) reads the opened binder's `userName`
via `lctx.fvarIdToDecl.find!`. Under the invariant, the declaration is exactly
the one `withLocalDecl`/`withLocalDef` just pushed, so the produced
`BinderName` is `nameToBinder` of the *source* binder name — which is what
`Erases.lam`/`letE` expect. These are the pure facts behind that; they rest on
lean4lean's `PersistentHashMap` modeling axioms (the accepted boundary). -/

theorem LocalContext.find?_mkLocalDecl_self {lctx : LocalContext} {x : FVarId}
    (h1 : lctx.WF) (h2 : lctx.find? x = none)
    {n : Name} {ty : Expr} {bi : BinderInfo} :
    (lctx.mkLocalDecl x n ty bi).find? x =
      some (.cdecl lctx.decls.size x n ty bi .default) := by
  rw [(h1.mkLocalDecl h2).find?_eq_find?_toList, LocalContext.mkLocalDecl_toList]
  simp [List.find?, LocalDecl.fvarId]

theorem LocalContext.find?_mkLetDecl_self {lctx : LocalContext} {x : FVarId}
    (h1 : lctx.WF) (h2 : lctx.find? x = none)
    {n : Name} {ty val : Expr} {nd : Bool} :
    (lctx.mkLetDecl x n ty val nd).find? x =
      some (.ldecl lctx.decls.size x n ty val nd .default) := by
  rw [(h1.mkLetDecl h2).find?_eq_find?_toList, LocalContext.mkLetDecl_toList]
  simp [List.find?, LocalDecl.fvarId]
  rfl

/-- Looking up a *different* fvar is unaffected by pushing a local declaration —
what makes the telescope's outer binder names survive to the innermost context,
where `Erasure.mkAlt` reads them. -/
theorem LocalContext.find?_mkLocalDecl_of_ne {lctx : LocalContext} {x y : FVarId}
    (h1 : lctx.WF) (h2 : lctx.find? x = none)
    {n : Name} {ty : Expr} {bi : BinderInfo} (hne : y ≠ x) :
    (lctx.mkLocalDecl x n ty bi).find? y = lctx.find? y := by
  rw [(h1.mkLocalDecl h2).find?_eq_find?_toList, Lean.LocalContext.mkLocalDecl_toList,
    h1.find?_eq_find?_toList]
  simp only [List.find?_cons, Lean.LocalDecl.fvarId]
  rw [show (y == x) = false from by
    simp only [Bool.eq_false_iff, ne_eq, fvarId_beq_iff_eq]; exact hne]

/-- `fvarIdToDecl.find!` is a function of `find?`, so it transports along it. -/
theorem LocalContext.fvarIdToDecl_find!_congr {l1 l2 : LocalContext} {y : FVarId}
    (h : l1.find? y = l2.find? y) : l1.fvarIdToDecl.find! y = l2.fvarIdToDecl.find! y := by
  rw [Lean.LocalContext.find?, Lean.LocalContext.find?] at h
  simp [PersistentHashMap.find!, h]

theorem LocalContext.fvarIdToDecl_find!_of_find? {lctx : LocalContext}
    {x : FVarId} {d : LocalDecl} (h : lctx.find? x = some d) :
    lctx.fvarIdToDecl.find! x = d := by
  rw [LocalContext.find?] at h
  simp [PersistentHashMap.find!, h]

/-! ## `mkAlt`'s de Bruijn closing, as a pure function

`Erasure.mkAlt xs t` (Erasure.lean:259) abstracts the field binders `xs`
outermost-first, the *innermost* becoming `.bvar 0`. `closeAlt` is that loop,
and `mkLambdas_closeAlt_cons` is the identity that lets the alternative's
λ-telescope be peeled one binder at a time by `bridge_lam_case`. -/

/-- `Erasure.mkAlt`'s de Bruijn closing loop as a pure function: the `i`-th binder
counted *from the end* becomes `.bvar i`. -/
def closeAlt : List FVarId → LBTerm → LBTerm
  | [], t => t
  | x :: xs, t => toBvar x xs.length (closeAlt xs t)

/-- …and it is exactly the `for` loop `mkAlt` runs. -/
theorem closeAlt_foldl (xs : List FVarId) (t : LBTerm) :
    (xs.reverse.zipIdx).foldl (fun b p => toBvar p.1 p.2 b) t = closeAlt xs t := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons, List.zipIdx_append]
    simp only [List.foldl_append, List.length_reverse, List.zipIdx_cons, List.zipIdx_nil,
      List.foldl_cons, List.foldl_nil, ih, closeAlt]
    simp

/-- **Peeling one alternative binder.** `mkLambdas`-of-`closeAlt` on a cons is a
single `.lambda` over `toBvar x 0` of the rest — i.e. exactly the shape
`bridge_lam_case` produces. (This is where `toBvar_mkLambdas` earns its keep: the
outer binder's insertion level is the *number of inner binders*, and pushing it
under the `mkLambdas` chain is what re-indexes it to `0`.) -/
theorem mkLambdas_closeAlt_cons (N : BinderName) (Ns : List BinderName)
    (x : FVarId) (xs : List FVarId) (t : LBTerm) (h : Ns.length = xs.length) :
    mkLambdas (N :: Ns) (closeAlt (x :: xs) t)
      = .lambda N (toBvar x 0 (mkLambdas Ns (closeAlt xs t))) := by
  rw [toBvar_mkLambdas]
  simp only [mkLambdas, closeAlt, Nat.zero_add, h]

/-! Non-vacuity: the closing identity at depth 2 — `mkAlt [x₁,x₂] t`'s body is
`toBvar x₁ 1 (toBvar x₂ 0 t)`, and re-wrapping it as a λ-chain is the same as
peeling one binder at a time. -/
example (N₁ N₂ : BinderName) (x₁ x₂ : FVarId) (t : LBTerm) :
    mkLambdas [N₁, N₂] (closeAlt [x₁, x₂] t)
      = .lambda N₁ (toBvar x₁ 0 (.lambda N₂ (toBvar x₂ 0 t))) :=
  mkLambdas_closeAlt_cons N₁ [N₂] x₁ [x₂] t rfl

example (x₁ x₂ : FVarId) (t : LBTerm) :
    closeAlt [x₁, x₂] t = toBvar x₁ 1 (toBvar x₂ 0 t) := rfl

/-! ## The binder cases of the bridge, Erases-side core

`visitLambda`/`visitLet` open the binder into a fresh fvar `x`
(`lambdaMonocular`/`letMonocular`), erase in the extended context, and close the
result with `abstract x` = `toBvar x 0` (`mkLambda`/`mkLetIn`). These lemmas
package the Erases-side reasoning of those two cases: from the induction
hypothesis' output at the fvar-extended `Δ`, recover the `Erases` judgment for
the binder node itself, via `Erases.uninstantiate` (`ErasesAbstract.lean`) for
the opened body and `Erases.strengthen_vlet` (`ErasesStrengthen.lean`) for the
let-value (which the shipping code erases *inside* `withLocalDef`). Freshness of
`x` w.r.t. `Δ` supplies every `FVarsIn` side condition, and closedness of the
body comes from its own translation premise (`TrExprS.closed`) at an all-fvar
context (`Δ.NoBV` — the bridge's contexts mirror a real `LocalContext`, so they
contain no bvar entries). -/

theorem bridge_lam_case {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx}
    {x : FVarId} {deps : List FVarId} {ty b : Expr} {ty' body' : VExpr}
    {t' : LBTerm} {n : Name} {bi : BinderInfo}
    (hΔbv : Δ.NoBV)
    (hty : TrExprS env Us Δ ty ty')
    (hbody : TrExprS env Us ((none, .vlam ty') :: Δ) b body')
    (hx : x ∉ Δ.fvars)
    (IH : Erases env Us Γ ((some (x, deps), .vlam ty') :: Δ)
            (b.instantiate1' (.fvar x)) t') :
    Erases env Us Γ Δ (.lam n ty b bi) (.lambda (nameToBinder n) (toBvar x 0 t')) := by
  have hfv : FVarsIn (· ∈ Δ.fvars) b := by
    have := hbody.fvarsIn
    simpa [VLCtx.fvars] using this
  have sc : FVarsIn (· ≠ x) b := hfv.mono fun fv hfv' heq => hx (heq ▸ hfv')
  have hc : b.Closed 1 := by
    have := hbody.closed
    simpa [VLCtx.bvars, hΔbv] using this
  exact .lam hty (IH.uninstantiate sc hc)

theorem bridge_let_case {env : VEnv} {Us : List Name} {Γ : ErasureCtx} {Δ : VLCtx}
    {x : FVarId} {deps : List FVarId} {ty v b : Expr} {ty' val' body' : VExpr}
    {v'' t' : LBTerm} {n : Name} {nd : Bool}
    (hΔbv : Δ.NoBV)
    (hty : TrExprS env Us Δ ty ty')
    (hval : TrExprS env Us Δ v val')
    (hbody : TrExprS env Us ((none, .vlet ty' val') :: Δ) b body')
    (hx : x ∉ Δ.fvars)
    (IHv : Erases env Us Γ ((some (x, deps), .vlet ty' val') :: Δ) v v'')
    (IHb : Erases env Us Γ ((some (x, deps), .vlet ty' val') :: Δ)
             (b.instantiate1' (.fvar x)) t') :
    Erases env Us Γ Δ (.letE n ty v b nd)
      (.letIn (nameToBinder n) v'' (toBvar x 0 t')) := by
  have scv : FVarsIn (· ≠ x) v :=
    hval.fvarsIn.mono fun fv hfv' heq => hx (heq ▸ hfv')
  have hfvb : FVarsIn (· ∈ Δ.fvars) b := by
    have := hbody.fvarsIn
    simpa [VLCtx.fvars] using this
  have scb : FVarsIn (· ≠ x) b := hfvb.mono fun fv hfv' heq => hx (heq ▸ hfv')
  have hc : b.Closed 1 := by
    have := hbody.closed
    simpa [VLCtx.bvars, hΔbv] using this
  exact .letE hty hval (IHv.strengthen_vlet scv) (IHb.uninstantiate scb hc)

end LeanToLambdaBox
