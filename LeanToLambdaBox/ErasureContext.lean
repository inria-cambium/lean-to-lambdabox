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
  /-- For each source *constructor* name, its arity `cstr_arity = npars + nargs`
      (matching `Semantics/Env.constructorArity`). Used by the saturated-constructor
      source evaluation `SEvalData` to bound the number of accumulated arguments, and
      linked to the target-side `constructorArity` via `ErasesEnvCtor`. Defaulted to
      `none` so existing `ErasureCtx` literals need not mention it. -/
  ctorArities : Name → Option Nat := fun _ => none
  /-- For each source `casesOn`-like name, its `(InductiveId, #params)`. Used by
      `Erases` to recognise `casesOn` applications. -/
  casesOns : Name → Option (InductiveId × Nat) := fun _ => none
  /-- For each `InductiveId`, the per-constructor **field** counts in constructor-index
      order — `register_inductive`'s `nargs = Array.count .keep argmask`
      (`Erasure.lean:222`), i.e. the *retained* (post-argmask) fields, matching
      `ConstructorBody.nargs` and hence `Semantics/Env.constructorArity`'s
      `body.npars + cb.nargs` minus `npars`. Its length is the inductive's constructor
      count. `Erases.cases` uses it to pin each minor's binder telescope to its
      constructor's field arity, and the minor count to the constructor count.
      Defaulted to `none` so existing `ErasureCtx` literals need not mention it. -/
  ctorFields : InductiveId → Option (List Nat) := fun _ => none
  /-- For each registered `casesOn` head, the discriminant's position in the
      application spine — `CasesInfo.discrPos` = `numParams + 1 (motive) + numIndices`,
      i.e. the number of leading arguments `visitCases` drops into `pre`. Pins the
      `Erases.cases` spine split so that an **over-applied** `casesOn` cannot be
      mis-parsed (an over-application would otherwise be readable as a `casesOn` whose
      discriminant is the first minor, which erases to a stuck `.case`).
      Defaulted to `none`. -/
  casesDiscrPos : Name → Option Nat := fun _ => none

/-- Convert a Lean `Name` to a `BinderName` exactly as `Erasure.fvar_to_name` does. -/
def nameToBinder (n : Name) : BinderName :=
  let s := n.toString
  if s.all (fun (c : Char) => decide (33 ≤ c.toNat ∧ c.toNat < 127)) then .named s else .anon
