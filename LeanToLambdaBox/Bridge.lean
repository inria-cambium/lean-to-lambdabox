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

* **constructor heads** (`Γ.ctors`): the shipping emits the *applied* form
  `.construct iid cidx []` under an application spine, while `Erases.ctor` is the
  args-inside *block* form — bridging those needs an applied-form `Erases` rule
  and an `erases_correct` extension under `construct_app` semantics (future work);
* **projections**, **literals** (under `nat := .peano` a `Nat` literal routes
  into the constructor path; under `.machine` into `prim`), and **`mdata`**
  (`Erases` has no `mdata` rule);
* everything `visitExpr` itself panics on (`sort`, `forallE`, `mvar`).

Two spine-shaped rules extend it: `ctorApp` (saturated constructor applications,
the data fragment) and `casesApp` (saturated `casesOn` applications with
*manifest* λ minors and — for now, ι-T4a — zero-field alternatives, the ι
fragment). Both are documented at their constructors.

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
must belong to `known` — an abstract name class scoping the bridge's
state-agreement hypothesis "every `known` constant is pre-registered in the
`ErasureState` with its `Γ` kername" (a finite `constants` map cannot agree with
the *total* `Γ.constants` on all of `Name`, so the agreement must be scoped;
`known` is exactly that scope). -/
inductive Supported (known : Name → Prop) (Γ : ErasureCtx) : Expr → Prop
  | bvar (i : Nat) : Supported known Γ (.bvar i)
  | fvar (x : FVarId) : Supported known Γ (.fvar x)
  | const (n : Name) (us : List Level) (hk : known n)
      (hctor : Γ.ctors n = none) (hcases : Γ.casesOns n = none) :
      Supported known Γ (.const n us)
  | app {f a : Expr} (hf : Supported known Γ f) (ha : Supported known Γ a) :
      Supported known Γ (.app f a)
  | lam {b : Expr} (n : Name) (ty : Expr) (bi : BinderInfo)
      (hb : Supported known Γ b) : Supported known Γ (.lam n ty b bi)
  | letE {v b : Expr} (n : Name) (ty : Expr) (nd : Bool)
      (hv : Supported known Γ v) (hb : Supported known Γ b) :
      Supported known Γ (.letE n ty v b nd)
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

      **Fragment boundaries** (all deliberate, all needed by the model):
      * each minor is a **manifest** λ-telescope of at least its constructor's field
        count (`hlam`) — the eraser's `lambdaOrIntroToArity` intro branch η-expands,
        which `Erases` cannot model (no η rule). Lean's `match` compiler emits minors
        as explicit `fun a b => …`, so real pattern-matching code is inside the
        fragment; hand-written η-contracted minors (`Option.casesOn o none Some`) are
        not. Fixing that needs an `Erases`-level η rule, not more proof effort.
      * `hflat` — **temporary** (ι-T4a, the flat-alternative slice): every constructor
        has zero retained fields, so `lambdaOrIntroToArity … 0 k = k e []` and no
        binder is ever opened. This covers `Bool`, `Ordering`, `Decidable`-style
        dispatch and any enum match. ι-T4b deletes it (a weakening for producers).

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
      (hflat : ∀ j (h : j < nfs.length), nfs[j] = 0)
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
  | ctorApp hc hcases har hsat hzero hsucc _ ihargs =>
    rw [instantiate1'_foldl_app]
    simp only [Expr.instantiate1']
    refine .ctorApp hc hcases har (by simp [hsat]) hzero hsucc (fun i hi => ?_)
    rw [List.getElem_map]
    exact ihargs i (by simpa using hi) k
  | @casesApp con us iid np dp nfs pre minors discr hc hdp hnfs hpre hsat hflat hnat hint
      hdiscr hlam hminors ihdiscr ihminors =>
    rw [instantiate1'_foldl_app]
    simp only [Expr.instantiate1', List.map_append, List.map_cons]
    refine .casesApp (pre := pre.map (·.instantiate1' (.fvar x) k))
      (minors := minors.map (·.instantiate1' (.fvar x) k))
      (discr := discr.instantiate1' (.fvar x) k)
      hc hdp hnfs (by simp [hpre]) (by simp [hsat]) hflat hnat hint (ihdiscr k)
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

/-! Non-vacuity guards: the fragment is inhabited at every rule, and genuinely
excludes the unsupported constructs. -/

example : Supported (fun _ => True)
    ⟨fun _ => none, fun _ => ⟨.MPfile [], "x"⟩, fun _ => none, fun _ => none, fun _ => none,
      fun _ => none, fun _ => none⟩
    (.lam `x (.const `Nat []) (.bvar 0) .default) :=
  .lam _ _ _ (.bvar 0)

example {known : Name → Prop} {Γ : ErasureCtx} :
    ¬ Supported known Γ (.lit (.natVal 0)) := by
  intro h
  generalize he : (Expr.lit (Literal.natVal 0)) = e at h
  cases h with
  | @ctorApp cn us iid cidx ar args hc hcases har hsat hz hs hargs =>
      rcases List.eq_nil_or_concat args with rfl | ⟨i, l, rfl⟩ <;>
        simp only [List.foldl_nil, List.concat_eq_append, List.foldl_append,
          List.foldl_cons, List.foldl_nil] at he <;> exact absurd he (by simp)
  | @casesApp con us iid np dp nfs pre minors discr hc hdp hnfs hpre hsat hflat hnat hint
      hdiscr hlam hminors =>
      obtain ⟨g, a, hga⟩ := exists_app_of_foldl_app_ne_nil (Expr.const con us)
        (args := pre ++ discr :: minors) (by simp)
      rw [hga] at he; exact absurd he (by simp)
  | _ => simp_all

example {known : Name → Prop} {Γ : ErasureCtx} :
    ¬ Supported known Γ (.proj `Prod 0 (.fvar ⟨`p⟩)) := by
  intro h
  generalize he : (Expr.proj `Prod 0 (.fvar ⟨`p⟩)) = e at h
  cases h with
  | @ctorApp cn us iid cidx ar args hc hcases har hsat hz hs hargs =>
      rcases List.eq_nil_or_concat args with rfl | ⟨i, l, rfl⟩ <;>
        simp only [List.foldl_nil, List.concat_eq_append, List.foldl_append,
          List.foldl_cons, List.foldl_nil] at he <;> exact absurd he (by simp)
  | @casesApp con us iid np dp nfs pre minors discr hc hdp hnfs hpre hsat hflat hnat hint
      hdiscr hlam hminors =>
      obtain ⟨g, a, hga⟩ := exists_app_of_foldl_app_ne_nil (Expr.const con us)
        (args := pre ++ discr :: minors) (by simp)
      rw [hga] at he; exact absurd he (by simp)
  | _ => simp_all

/-- A saturated nullary constructor *is* in the fragment (`ctorApp`, `args = []`,
`ar = 0`). -/
example (iid : InductiveId) :
    Supported (fun _ => True)
      ⟨fun _ => none, fun _ => ⟨.MPfile [], "x"⟩,
        fun n => if n = `c then some (iid, 0) else none,
        fun n => if n = `c then some 0 else none, fun _ => none,
        fun _ => none, fun _ => none⟩
      (.const `c []) := by
  have h : (Expr.const `c []) = ([] : List Expr).foldl Expr.app (.const `c []) := rfl
  rw [h]
  refine .ctorApp (iid := iid) (cidx := 0) (ar := 0) (args := []) ?_ rfl ?_ rfl ?_ ?_ ?_
  · simp
  · simp
  · decide
  · decide
  · intro i hi; exact absurd hi (by simp)

/-- A saturated `casesOn` application *is* in the fragment (`casesApp`, flat
alternatives): `J` has one parameter and one index, so the motive and the index
push the discriminant to `dp = 3 ≠ numParams`; two constructors with no retained
fields give two `.fvar` minors. Exercises `hpre` at a `dp` that is *not* the
parameter count — the pin that stops an over-applied `casesOn` from being
re-parsed with the first minor as discriminant. -/
example (iid : InductiveId) (p m i d a b : FVarId) :
    Supported (fun _ => True)
      ⟨fun _ => none, fun _ => ⟨.MPfile [], "x"⟩, fun _ => none, fun _ => none,
        fun n => if n = `J.casesOn then some (iid, 1) else none,
        fun _ => some [0, 0],
        fun n => if n = `J.casesOn then some 3 else none⟩
      ([Expr.fvar p, .fvar m, .fvar i, .fvar d, .fvar a, .fvar b].foldl Expr.app
        (.const `J.casesOn [])) := by
  have h : ([Expr.fvar p, .fvar m, .fvar i, .fvar d, .fvar a, .fvar b] : List Expr)
      = [Expr.fvar p, .fvar m, .fvar i] ++ Expr.fvar d :: [Expr.fvar a, .fvar b] := rfl
  rw [h]
  refine .casesApp (iid := iid) (np := 1) (dp := 3) (nfs := [0, 0]) (by simp) (by simp) rfl
    rfl rfl ?_ (by decide) (by decide) (.fvar d) ?_ ?_
  · intro j hj
    match j, hj with
    | 0, _ => rfl
    | 1, _ => rfl
  · intro j hj
    match j, hj with
    | 0, _ => trivial
    | 1, _ => trivial
  · intro j hj
    match j, hj with
    | 0, _ => exact .fvar a
    | 1, _ => exact .fvar b

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

theorem LocalContext.fvarIdToDecl_find!_of_find? {lctx : LocalContext}
    {x : FVarId} {d : LocalDecl} (h : lctx.find? x = some d) :
    lctx.fvarIdToDecl.find! x = d := by
  rw [LocalContext.find?] at h
  simp [PersistentHashMap.find!, h]

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
