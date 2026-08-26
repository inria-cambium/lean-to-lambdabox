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
  /-- `true` when the run erases in **peano-`Nat`** mode (`ErasureConfig.nat = .peano`), so
      `Nat` literals become the constructor tower rather than `.prim`.

      `Supported` (`Bridge.lean`) is purely syntactic in `(known, Γ)` and cannot see the
      shipping reader's `ctx.config`; registration (`register_inductive`) registers `Nat`'s
      constructors under *both* configs, so `Γ` alone cannot tell peano from machine. This
      flag carries that one bit into `Γ`, where `Supported.natLit` reads it (and where the
      bridge cashes it in against the run). Defaulted to `false`, so every machine-mode
      consumer is unchanged and the literal rule is unusable at the default `Γ`. -/
  natPeano : Bool := false
  /-- For each source name that is a **sibling of the mutual block currently being
      erased**, the fresh `FVarId` the run minted for it (`Erasure.visitMutual`, the
      `withReader … fixvars` line). Mirrors the shipping reader's
      `ErasureContext.fixvars` one-for-one, which is what makes the bridge's fixvar
      branch cheap (`BridgeInv.fixvars` is a plain agreement between the two).

      Non-`none` only *inside* a block; every top-level `Γ` leaves it at `fun _ => none`.
      Read by the `Erases.fixvar` leaf (`.const nm us ↦ .fvar x`, slice W3.1), which is
      why `Γ.fixvars = fun _ => none` is a premise (`hnfv`) of every forward simulation:
      that equation is what refutes the leaf's `const_inv` disjunct in the δ cases, the
      way `NoFix` used to. Defaulted, like every registration field. (Recursion wall,
      slices W1 + W3.1.) -/
  fixvars : Name → Option FVarId := fun _ => none
  /-- For each **registered recursive constant**, the emitted mutual block and this
      constant's index in it — the datum `visitMutual` registers when it conses
      `(kn, .constantDecl ⟨some (.fix defs j)⟩)` onto the target env.

      This is what makes `Erases.fix` say something: the rule's `hreg` premise demands
      that `Γ` records *this* block for the block's own names, and the `const_fix` leaf
      relates a registered recursive constant to its own `.fix` node — which is what a
      fix *unfolding* puts where the source has a sibling `.const nⱼ`. Defaulted to
      `fun _ => none`, so both rules are unusable at a `Γ` that registers no recursion.
      (Recursion wall, slice W1.) -/
  recBodies : Name → Option (List (@FixDef LBTerm) × Nat) := fun _ => none

/-- **The block-local context**: `Γ` with a fixvar map installed, and *nothing else*
changed — the model of `visitMutual`'s
`withReader (fun env => { env with fixvars := … })` (`Erasure.lean`).

Every other registration field is literally `Γ`'s, which is what makes
`Erases.instFixvars`' non-fixvar arms `rfl` transports between the two contexts.
(Recursion wall, slice W3.1.) -/
def ErasureCtx.withFixvars (Γ : ErasureCtx) (fv : Name → Option FVarId) : ErasureCtx :=
  { Γ with fixvars := fv }

@[simp] theorem ErasureCtx.withFixvars_fixvars (Γ : ErasureCtx) (fv : Name → Option FVarId) :
    (Γ.withFixvars fv).fixvars = fv := rfl
@[simp] theorem ErasureCtx.withFixvars_constants (Γ : ErasureCtx) (fv : Name → Option FVarId) :
    (Γ.withFixvars fv).constants = Γ.constants := rfl
@[simp] theorem ErasureCtx.withFixvars_ctors (Γ : ErasureCtx) (fv : Name → Option FVarId) :
    (Γ.withFixvars fv).ctors = Γ.ctors := rfl
@[simp] theorem ErasureCtx.withFixvars_casesOns (Γ : ErasureCtx) (fv : Name → Option FVarId) :
    (Γ.withFixvars fv).casesOns = Γ.casesOns := rfl
@[simp] theorem ErasureCtx.withFixvars_casesDiscrPos (Γ : ErasureCtx)
    (fv : Name → Option FVarId) :
    (Γ.withFixvars fv).casesDiscrPos = Γ.casesDiscrPos := rfl
@[simp] theorem ErasureCtx.withFixvars_ctorFields (Γ : ErasureCtx) (fv : Name → Option FVarId) :
    (Γ.withFixvars fv).ctorFields = Γ.ctorFields := rfl
@[simp] theorem ErasureCtx.withFixvars_recBodies (Γ : ErasureCtx) (fv : Name → Option FVarId) :
    (Γ.withFixvars fv).recBodies = Γ.recBodies := rfl
/-- The three projections the original W3.1 list forgot. They hold by `rfl` like the
others, but until they are `@[simp]` a `simp` at a block-local `Γ.withFixvars fv` leaves
`(Γ.withFixvars fv).ctorArities` (motives 2/3/13/14), `.natPeano` (`BridgeInv.natcfg`) and
`.inductives` unreduced — which is exactly what the D8 instantiation walks into. -/
@[simp] theorem ErasureCtx.withFixvars_ctorArities (Γ : ErasureCtx)
    (fv : Name → Option FVarId) :
    (Γ.withFixvars fv).ctorArities = Γ.ctorArities := rfl
@[simp] theorem ErasureCtx.withFixvars_natPeano (Γ : ErasureCtx) (fv : Name → Option FVarId) :
    (Γ.withFixvars fv).natPeano = Γ.natPeano := rfl
@[simp] theorem ErasureCtx.withFixvars_inductives (Γ : ErasureCtx)
    (fv : Name → Option FVarId) :
    (Γ.withFixvars fv).inductives = Γ.inductives := rfl

/-- Convert a Lean `Name` to a `BinderName` exactly as `Erasure.fvar_to_name` does. -/
def nameToBinder (n : Name) : BinderName :=
  let s := n.toString
  if s.all (fun (c : Char) => decide (33 ≤ c.toNat ∧ c.toNat < 127)) then .named s else .anon
