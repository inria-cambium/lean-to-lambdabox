import LeanToLambdaBox.Basic

/-!
# Erasure context

The static context relating source-side Lean `Name`s to target-side λ□ identifiers,
used by the typed erasure relation `LeanToLambdaBox.Erases` (over real `Lean.Expr`)
and the pure erasure core `eraseCore`. Abstracting these lookups as a parameter
lets the erasure relation avoid traversing the global environment.
-/

open Lean

/--
Context relating source-side names to target-side identifiers. The shipping
erasure function (`Erasure.lean`) builds this implicitly via `register_inductive`
and the `constants`/`inductives` fields of `ErasureState`; here it is abstracted
as a parameter.
-/
structure ErasureCtx where
  /-- For each source inductive type name, the corresponding `InductiveId`. -/
  inductives : Name → Option InductiveId
  /-- For each source constant, the kername it is bound to on the target side. -/
  constants  : Name → Kername
  /-- For each source *constructor* name, its `(InductiveId, constructor index)`
      as `register_inductive` assigns it. Used by `Erases` to recognise
      constructor applications. -/
  ctors : Name → Option (InductiveId × Nat) := fun _ => none
  /-- For each source `casesOn`-like name, its `(InductiveId, #params)`. Used by
      `Erases` to recognise `casesOn` applications. -/
  casesOns : Name → Option (InductiveId × Nat) := fun _ => none

/-- Convert a Lean `Name` to a `BinderName` exactly as `Erasure.fvar_to_name` does. -/
def nameToBinder (n : Name) : BinderName :=
  let s := n.toString
  if s.all (fun (c : Char) => decide (33 ≤ c.toNat ∧ c.toNat < 127)) then .named s else .anon
