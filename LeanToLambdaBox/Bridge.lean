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
* **`casesOn` heads** (`Γ.casesOns`), **projections**, **literals** (under
  `nat := .peano` a `Nat` literal routes into the constructor path; under
  `.machine` into `prim`), and **`mdata`** (`Erases` has no `mdata` rule);
* everything `visitExpr` itself panics on (`sort`, `forallE`, `mvar`).

`bvar` *is* in the fragment even though `visitExpr`'s `.bvar` case is
`unreachable!` on the locally-closed terms it actually visits: the predicate is
purely syntactic and must be closed under going below binders; recursion always
instantiates the binder with a fresh fvar first (`Supported.instantiate1'`).
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

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
    ⟨fun _ => none, fun _ => ⟨.MPfile [], "x"⟩, fun _ => none, fun _ => none⟩
    (.lam `x (.const `Nat []) (.bvar 0) .default) :=
  .lam _ _ _ (.bvar 0)

example {known : Name → Prop} {Γ : ErasureCtx} :
    ¬ Supported known Γ (.lit (.natVal 0)) := by rintro ⟨⟩

example {known : Name → Prop} {Γ : ErasureCtx} :
    ¬ Supported known Γ (.proj `Prod 0 (.fvar ⟨`p⟩)) := by rintro ⟨⟩

/-- A registered-constructor head is excluded. -/
example (iid : InductiveId) :
    ¬ Supported (fun _ => True)
      ⟨fun _ => none, fun _ => ⟨.MPfile [], "x"⟩,
        fun _ => some (iid, 0), fun _ => none⟩
      (.const `c []) := by
  rintro ⟨_, _, _, hctor, _⟩; simp_all

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
