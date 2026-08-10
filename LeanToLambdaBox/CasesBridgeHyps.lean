import LeanToLambdaBox.ErasureRun
import LeanToLambdaBox.ErasureContext
import Lean4Lean.Verify.NameGenerator
import Lean4Lean.Verify.Axioms

/-!
# The ι-fragment trust bundle: `CasesBridgeHyps`

This structure sits *beside* `BridgeHyps` (`VisitExprRefines.lean`) and
`DataBridgeHyps` (`DataBridgeHyps.lean`), and carries the Hoare-style
specifications the `visitExpr`→`Erases` bridge needs to cover the **saturated
`casesOn`** fragment (`Supported.casesApp`, `Bridge.lean`) — the ι (C4)
extension of the bridge to pattern matching.

It is a *separate* bundle rather than extra fields on `DataBridgeHyps` so that
the β+δ+ctor stack's premise set stays pinned: `DataBridgeHyps` is byte-unchanged
and every theorem stated against it keeps its exact meaning.

Four clauses, over the same ghost world-measure `gw : Void IO.RealWorld →
NameGenerator` used by the other two bundles. All the runtime primitives they
spec (`getCasesInfo?`, `getConstInfo`, `register_inductive`, `Meta.inferType`)
are **real** — not part of the `visitExpr` mutual block — so their Hoare specs
are usable directly inside the fixpoint induction.

* `cases_run_pos` — `getCasesInfo?` is *positive* on a registered `casesOn` head,
  and returns the **plain-`casesOn`** shape agreeing with `Γ`
  (`BridgeHyps.cases_run` gives only the negative direction; this is its positive
  twin, exactly as `DataBridgeHyps.ctor_run` is the positive twin of
  `BridgeHyps.ctor_run`).
* `casesind_run` — `getConstInfo con.getPrefix` returns the `casesOn`'s inductive,
  whose `numParams` matches `Γ.casesOns`. Monotone, state-preserving.
* `casesreg_run` — `register_inductive` on that inductive returns `Γ`'s
  `InductiveId` and one **trivial** argmask per constructor, of the declared field
  width (the same assumption `DataBridgeHyps.reg_run` makes on the constructor
  path: relevant fields, default `remove_irrel_constr_args := false`,
  pre-registered inductive). State-preserving, monotone.
* `infer_lam_run` — the `Meta.inferType` spec: on a manifest λ-telescope it
  returns a `∀`-telescope matching it binder-for-binder (same binder **name**,
  same **domain**). Purely syntactic — no typing content, no `whnf`, no defeq;
  it is what `Lean.Meta.inferLambdaType` computes (`lambdaTelescope e fun xs b =>
  mkForallFVars xs (← inferType b)` re-abstracts the very fvars `lambdaTelescope`
  introduced from the λ's own binders). Same epistemic class as
  `BridgeHyps.orc_run`, but human-checkable against a four-line library function.

**Trust ledger.** Three of the four are Γ↔environment *registration* agreements
(discharged in practice by the same DAG cold-start that discharges
`RegisteredCases`); the fourth is a syntactic fact about one library function.
All four are `env`/`Us`-free: **the ι bridge adds no typing assumption**.
Because they quantify over opaque runtime primitives their global satisfiability
is not in-logic decidable — the documented trust boundary, exactly as for
`BridgeHyps`/`DataBridgeHyps`.

`infer_lam_run` is the only clause the flat-alternative slice (ι-T4a) did not
need; the general-alternative slice (ι-T4b) uses it to open each minor's binder
through the inferred type. All the *typing* data that opening needs
(`TrExprS`/`IsType` for the domain) still comes from inverting the minor's own
`TrExprS.lam`, which is why `infer_lam_run` stays purely syntactic.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

/-- `ty` is a `∀`-telescope matching `e`'s λ-telescope binder-for-binder (name
**and** domain), as deep as `e`'s λ-prefix goes.

This must be stated *telescopically*: `Erasure.visitAlt` calls `inferType`
**once** and `lambdaOrIntroToArity` threads the codomain down without
re-inferring, so a single-level statement would not survive to level 2. It is
vacuously true as soon as `e` stops being a λ, so it is safe to state for all
pairs.

The middle clause (a λ forces a `∀`) is **load-bearing**, not decoration: the
eraser's `forallMonocular` destructures the type with `let .forallE … | unreachable!`,
and `unreachable!` at `EraseM` *succeeds* with `default` rather than failing
(`Erasure.run_panicWithPosWithDecl`). Without it a run that fell through the panic
would satisfy the hypotheses and refute the conclusion. It is equally true of
`Lean.Meta.inferLambdaType`, whose output on a λ is a `mkForallFVars`. -/
def ForallMatchesLam : Expr → Expr → Prop
  | .forallE n d c _, .lam m a b _ => n = m ∧ d = a ∧ ForallMatchesLam c b
  | _,                .lam _ _ _ _ => False
  | _,                _            => True

/-- `ForallMatchesLam` is vacuous unless the *type* side is a `∀`… -/
theorem forallMatchesLam_of_not_forallE {ty e : Expr}
    (h : ∀ n d c bi, ty ≠ .forallE n d c bi) (hl : ∀ n a b bi, e ≠ .lam n a b bi) :
    ForallMatchesLam ty e := by
  cases ty with
  | forallE n d c bi => exact absurd rfl (h n d c bi)
  | _ =>
    cases e with
    | lam m a b bi' => exact absurd rfl (hl m a b bi')
    | _ => trivial

/-- …and unless the *term* side is a λ. -/
theorem forallMatchesLam_of_not_lam {ty e : Expr}
    (h : ∀ n a b bi, e ≠ .lam n a b bi) : ForallMatchesLam ty e := by
  cases ty with
  | forallE n d c bi =>
    cases e with
    | lam m a b bi' => exact absurd rfl (h m a b bi')
    | _ => trivial
  | _ =>
    cases e with
    | lam m a b bi' => exact absurd rfl (h m a b bi')
    | _ => trivial

/-- Substituting a *free variable* never creates a `∀` head… -/
theorem instantiate1'_fvar_not_forallE {e : Expr} (x : FVarId) (k : Nat)
    (h : ∀ n d c bi, e ≠ .forallE n d c bi) :
    ∀ n d c bi, e.instantiate1' (.fvar x) k ≠ .forallE n d c bi := by
  intro n d c bi
  cases e with
  | bvar i =>
    simp only [Expr.instantiate1']
    split
    · simp
    · split
      · simp [Expr.liftLooseBVars']
      · simp
  | forallE a b c d => exact absurd rfl (h a b c d)
  | _ => simp [Expr.instantiate1']

/-- …nor a λ head. -/
theorem instantiate1'_fvar_not_lam {e : Expr} (x : FVarId) (k : Nat)
    (h : ∀ n a b bi, e ≠ .lam n a b bi) :
    ∀ n a b bi, e.instantiate1' (.fvar x) k ≠ .lam n a b bi := by
  intro n a b bi
  cases e with
  | bvar i =>
    simp only [Expr.instantiate1']
    split
    · simp
    · split
      · simp [Expr.liftLooseBVars']
      · simp
  | lam p q r t => exact absurd rfl (h p q r t)
  | _ => simp [Expr.instantiate1']

/-- **The binder-for-binder match survives opening a binder.** Both sides descend
at the same de Bruijn depth, which is exactly what `lambdaMonocularOrIntro` does
(it instantiates the ∀'s codomain and the λ's body with the *same* fresh fvar).
The substituend is restricted to an fvar — for a general substituend the claim is
false, since a `.bvar` could be replaced by a λ. -/
theorem ForallMatchesLam.instantiate1' {ty e : Expr} (x : FVarId) :
    ForallMatchesLam ty e → ∀ k, ForallMatchesLam (ty.instantiate1' (.fvar x) k)
      (e.instantiate1' (.fvar x) k) := by
  induction ty generalizing e with
  | forallE n d c bi ihd ihc =>
    cases e with
    | lam m a b bi' =>
      intro h k
      obtain ⟨h1, h2, h3⟩ := h
      exact ⟨h1, by rw [h2], ihc h3 (k + 1)⟩
    | _ =>
      intro _ k
      exact forallMatchesLam_of_not_lam (instantiate1'_fvar_not_lam x k (by intro _ _ _ _; simp))
  | _ =>
    intro h k
    refine forallMatchesLam_of_not_forallE
      (instantiate1'_fvar_not_forallE x k (by intro _ _ _ _; simp))
      (instantiate1'_fvar_not_lam x k ?_)
    intro nn aa bb bb'
    cases e with
    | lam p q r t => exact absurd h id
    | _ => simp

/-- The runtime `CasesInfo` for `con` has the *plain `casesOn`* shape and agrees
with `Γ`'s metadata: the discriminant sits at `dp`, there is **no**
per-constructor side condition and **no** sparse catch-all
(`altsRange = dp+1 ... arity`, every alternative a `.ctor` with its constructor's
field count), and there is exactly one alternative per constructor.

`Lean.CasesInfo`'s own docstring lists three shapes `getCasesInfo?` recognises:
plain `casesOn`, per-constructor eliminations (side condition + one alternative),
and *sparse* cases-on (some constructors + a `.default` catch-all). Only the
plain shape can produce a well-formed λ□ `.case`; the other two are excluded
here, and `Erases.cases`' `hnlen` makes them underivable — the model rejects what
the eraser mis-handles (see the findings note in the ι-T4 commit). -/
structure CasesInfoAgrees (ci : CasesInfo) (con : Name) (dp : Nat) (nfs : List Nat) : Prop where
  /-- The `CasesInfo` is the one for `con`. -/
  declName : ci.declName = con
  /-- The discriminant position matches `Γ.casesDiscrPos`. -/
  discrPos : ci.discrPos = dp
  /-- Exactly `dp` dropped arguments, one discriminant, one minor per constructor. -/
  arity    : ci.arity = dp + 1 + nfs.length
  /-- No side condition: the alternatives start right after the discriminant. -/
  range    : ci.altsRange = ⟨dp + 1, ci.arity⟩
  /-- One alternative per constructor. -/
  numAlts  : ci.altNumParams.size = nfs.length
  /-- Every alternative is a genuine constructor alternative (no `.default`
  catch-all) binding exactly its constructor's fields. -/
  alts     : ∀ j (h : j < nfs.length), ∃ cn, ci.altNumParams[j]! = .ctor cn (nfs[j]'h)

/-- The ι-fragment trust bundle (see module docstring). -/
structure CasesBridgeHyps (Γ : ErasureCtx) (gw : Void IO.RealWorld → NameGenerator) : Prop where
  /-- `getCasesInfo?` is **positive** on a registered `casesOn` head, and the
  returned `CasesInfo` has the plain-`casesOn` shape agreeing with `Γ`. -/
  cases_run_pos : ∀ (con : Name) (iid : InductiveId) (np dp : Nat) (nfs : List Nat)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (r : Option CasesInfo) (w₁ : Void IO.RealWorld),
    Γ.casesOns con = some (iid, np) → Γ.casesDiscrPos con = some dp →
    Γ.ctorFields iid = some nfs →
    getCasesInfo? con cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧ ∃ ci, r = some ci ∧ CasesInfoAgrees ci con dp nfs
  /-- `getConstInfo con.getPrefix` returns the `casesOn`'s inductive, whose
  `numParams` matches `Γ.casesOns`. Monotone, state-preserving. -/
  casesind_run : ∀ (con : Name) (iid : InductiveId) (np : Nat)
    (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (ci : ConstantInfo)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Γ.casesOns con = some (iid, np) →
    (getConstInfo con.getPrefix : EraseM ConstantInfo) s ctx cctx ref w = .ok (ci, s₁) w₁ →
    gw w ≤ gw w₁ ∧ s = s₁ ∧
      ∃ indVal : InductiveVal, ci = .inductInfo indVal ∧ indVal.numParams = np ∧
        indVal.name = con.getPrefix
  /-- `register_inductive` on that inductive returns `Γ`'s `InductiveId` and one
  **trivial** argmask per constructor, of the declared field width.
  State-preserving (the inductive is pre-registered). -/
  casesreg_run : ∀ (indVal : InductiveVal) (con : Name) (iid : InductiveId) (np : Nat)
    (nfs : List Nat) (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld)
    (r : InductiveId × InductiveArgMasks) (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Γ.casesOns con = some (iid, np) → Γ.ctorFields iid = some nfs →
    indVal.name = con.getPrefix →
    register_inductive indVal s ctx cctx ref w = .ok (r, s₁) w₁ →
    gw w ≤ gw w₁ ∧ s = s₁ ∧ r.1 = iid ∧ r.2.length = nfs.length ∧
      ∀ j (h : j < nfs.length), r.2[j]! = Array.replicate (nfs[j]'h) .keep
  /-- **The `inferType` spec.** `Meta.inferType` returns a `∀`-telescope matching
  its argument's λ-telescope binder-for-binder (same binder name, same domain).
  Purely syntactic; see the module docstring. -/
  infer_lam_run : ∀ (e : Expr)
    (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (ty : Expr)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Erasure.liftMetaM (Lean.Meta.inferType e) s ctx cctx ref w = .ok (ty, s₁) w₁ →
    gw w ≤ gw w₁ ∧ ForallMatchesLam ty e

/-! ## Non-vacuity guards

`CasesBridgeHyps` itself quantifies over opaque runtime primitives, so it cannot
be constructed in-logic — that is the documented trust boundary (the bridge's
guard instantiates every *other* premise instead, `VisitExprRefines.lean`). The
two auxiliary predicates *are* checked non-vacuous here. -/

/-- `CasesInfoAgrees` is inhabited at the shape the fragment targets: `J` with one
parameter and one index (so the motive and the index push the discriminant to
`discrPos = 3`) and two zero-field constructors. -/
example : CasesInfoAgrees
    ⟨`J.casesOn, `J, 6, 3, ⟨4, 6⟩, #[.ctor `J.a 0, .ctor `J.b 0]⟩ `J.casesOn 3 [0, 0] where
  declName := rfl
  discrPos := rfl
  arity := rfl
  range := rfl
  numAlts := rfl
  alts := by
    intro j hj
    match j, hj with
    | 0, _ => exact ⟨`J.a, rfl⟩
    | 1, _ => exact ⟨`J.b, rfl⟩

/-- `ForallMatchesLam` is inhabited at a genuine (dependently-typed) depth-2
λ-telescope and its inferred `∀`-telescope — the shape `Lean.Meta.inferLambdaType`
produces, and the one `infer_lam_run` asserts. -/
example : ForallMatchesLam
    (.forallE `a (.const `Nat []) (.forallE `b (.app (.const `V []) (.bvar 0))
      (.const `Nat []) .default) .default)
    (.lam `a (.const `Nat []) (.lam `b (.app (.const `V []) (.bvar 0))
      (.bvar 1) .default) .default) :=
  ⟨rfl, rfl, rfl, rfl, trivial⟩

end LeanToLambdaBox
