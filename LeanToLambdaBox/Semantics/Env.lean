import LeanToLambdaBox.Semantics.Substitution

/-!
# Global-environment queries for the λ□ semantics

Metadata lookups on the erased global environment that the operational semantics
and the `optimize` pass need: notably whether an inductive lives in `Prop`
(MetaCoq's `inductive_isprop_and_pars`), which guards the prop-case reduction
rules (`iota_sing`, `proj_prop`) and the `optimize` collapse.
-/

namespace LeanToLambdaBox

open Lean

/-- Is the inductive `iid` propositional? Lookup chain:
    `envLookup Γ iid.mutualBlockName` → `some (.inductiveDecl body)` →
    `body.bodies[iid.idx]?` → `OneInductiveBody.propositional`.

    MetaCoq analogue: the `true` component of `inductive_isprop_and_pars Σ ind`. -/
def isPropositionalInductive (Γ : GlobalDeclarations) (iid : InductiveId) : Bool :=
  match LBTerm.envLookup Γ iid.mutualBlockName with
  | some (.inductiveDecl body) =>
    match body.bodies[iid.idx]? with
    | some oib => oib.propositional
    | none => false
  | _ => false

/-- Does `LBOptimize`/the prop-case rule collapse this case?  `true` exactly when
    the inductive is propositional *and* the branch list is a single branch. -/
def wouldCollapse (Γ : GlobalDeclarations) (iid : InductiveId)
    (alts : List (List BinderName × LBTerm)) : Bool :=
  isPropositionalInductive Γ iid &&
    (match alts with | [_] => true | _ => false)

/-- Arity (number of arguments) of constructor `c` of inductive `iid`. Lookup chain:
    `envLookup Γ iid.mutualBlockName` → `some (.inductiveDecl body)` →
    `body.bodies[iid.idx]?` → `oib.ctors[c]?` → `ConstructorBody.nargs`.

    Used to bound the accumulation of a non-block (applied) constructor
    (MetaCoq's `cstr_arity`). -/
def constructorArity (Γ : GlobalDeclarations) (iid : InductiveId) (c : Nat) : Option Nat :=
  match LBTerm.envLookup Γ iid.mutualBlockName with
  | some (.inductiveDecl body) =>
    match body.bodies[iid.idx]? with
    | some oib => (oib.ctors[c]?).map (·.nargs)
    | none => none
  | _ => none

end LeanToLambdaBox
