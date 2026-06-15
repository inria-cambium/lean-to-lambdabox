import LeanToLambdaBox.Semantics

/-!
# Big-step weak call-by-value evaluation for λ□ (step A3.1)

This is the operational semantics our erased terms actually run under
(MetaCoq's `EWcbvEval`, the model peregrine→malfunction→OCaml implement),
restricted to the projection-free / fix-free fragment the typed `Erases`
currently covers.

The load-bearing rule for erasure soundness is `app_box` (MetaCoq's `eval_box`):
applying an irrelevant head (which erased to `box`) yields `box`. It is what
makes erasing partially-applied proofs/type-formers sound.

Constructors are evaluated in the **abstract args-inside form** `.construct iid k
args` (so a saturated constructor is a self-contained value and `iota` is direct);
the wrapping of the implementation's literal `.construct iid k []`-applied output
into this form is anchored in Half B.

`fix`/`proj` are deliberately absent (out of the current fragment).
-/

namespace LeanToLambdaBox

open Lean

/-- Weak call-by-value big-step evaluation of λ□ terms to values, relative to a
global environment `Γ` (for δ-reduction of constants). -/
inductive Eval (Γ : GlobalDeclarations) : LBTerm → LBTerm → Prop
  /-- Irrelevant marker is already a value. -/
  | box : Eval Γ .box .box
  /-- λ-abstractions are values (weak: no reduction under binders). -/
  | lam (n : BinderName) (b : LBTerm) : Eval Γ (.lambda n b) (.lambda n b)
  /-- Free variables are values. -/
  | fvar (x : FVarId) : Eval Γ (.fvar x) (.fvar x)
  /-- Primitives are values. -/
  | prim (p : PrimVal) : Eval Γ (.prim p) (.prim p)
  /-- β: the function evaluates to a λ, the argument to a value, then the body
      with the argument substituted evaluates to the result. -/
  | beta {f a : LBTerm} {n : BinderName} {b av r : LBTerm} :
      Eval Γ f (.lambda n b) → Eval Γ a av → Eval Γ (LBTerm.subst1 av b) r →
      Eval Γ (.app f a) r
  /-- `eval_box`: applying an irrelevant (boxed) head yields `box`. -/
  | app_box {f a : LBTerm} : Eval Γ f .box → Eval Γ (.app f a) .box
  /-- ζ: let-binding evaluates the value then the body with it substituted. -/
  | zeta {n : BinderName} {v b vv r : LBTerm} :
      Eval Γ v vv → Eval Γ (LBTerm.subst1 vv b) r → Eval Γ (.letIn n v b) r
  /-- δ: unfold a defined constant and evaluate its body. -/
  | delta {kn : Kername} {body r : LBTerm} :
      LBTerm.envLookup Γ kn = some (.constantDecl ⟨some body⟩) → Eval Γ body r →
      Eval Γ (.const kn) r
  /-- Constructor: evaluate each argument (the head is already saturated in the
      abstract form). -/
  | construct {iid : InductiveId} {k : Nat} {args vs : List LBTerm}
      (hl : args.length = vs.length)
      (hargs : ∀ i (h : i < args.length), Eval Γ args[i] (vs[i]'(hl ▸ h))) :
      Eval Γ (.construct iid k args) (.construct iid k vs)
  /-- ι: case analysis — the discriminant evaluates to a constructor, select the
      matching alternative and evaluate its body with the constructor's args
      substituted for the field binders. -/
  | iota {iid : InductiveId} {np k : Nat} {discr : LBTerm}
         {alts : List (List BinderName × LBTerm)} {cargs : List LBTerm}
         {names : List BinderName} {body r : LBTerm} :
      Eval Γ discr (.construct iid k cargs) →
      alts[k]? = some (names, body) →
      Eval Γ (LBTerm.substList cargs body) r →
      Eval Γ (.case (iid, np) discr alts) r

end LeanToLambdaBox
