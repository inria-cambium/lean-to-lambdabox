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
  /-- For each source **structure type** name `S` — the head of an `Expr.proj S i e` —
      its `(InductiveId, numParams)`, as `register_inductive` assigns the id and
      `InductiveVal.numParams` gives the count. This is exactly the pair `visitProj`
      (`Erasure.lean`) puts into `ProjectionInfo.indType` / `ProjectionInfo.paramCount`.

      Keyed by the **structure type** name, not by a constructor or a `casesOn` head, and
      that is why it is a new field rather than a derived lookup: `Expr.proj S i e` names
      only `S`, while `Γ.ctorArities` is keyed on the constructor and `Γ.casesOns` is
      populated only when the walk actually saw a `casesOn` application — which a
      projection-only structure never produces.

      Registered only for `register_inductive`'s `is_struct` shape
      (`names.length == 1 && inf.ctors.length == 1 && !inf.isRec`), which is what makes the
      target `WcbvEval.proj` rule's hard-wired constructor index `0` correct.
      Single-constructor-ness and the field count come free from
      `Γ.ctorFields iid = some [nf]`, so no separate `isStructure` bit is needed.

      Defaulted to `fun _ => none`, like every registration field, so every existing
      `ErasureCtx` literal is unchanged and `Erases.proj`/`Supported.proj` are unusable at
      a `Γ` that registers no structure. (Projection round, slice P0.) -/
  projs : Name → Option (InductiveId × Nat) := fun _ => none
  /-- For each source constant, its **declared universe parameters** — the
      `ConstantInfo.levelParams` the kernel unfolds it at, and the list
      `visitMutual` installs into the reader (`withReader (… lparams := ci.levelParams)`).

      This is the `Ups` map the Γ-U analysis (`DeltaHyps`, §Γ-U, finding (b)) said a
      universe-aware δ step has to be indexed by, and this column is its home. The
      alternative homes were an `Esrc`-side pairing (`SEnv := Name → Option (List Name ×
      Expr)`, which moves every `Esrc n = some body` site in the development) and a fresh
      parameter of the evaluation relations (which moves every `SEvalDataι Γ ia E`
      occurrence). `Γ` wins on two counts: it is already in scope at exactly the rules
      that need the map — `SEvalDataι.delta` and the δ case of `erases_correct_dataι` —
      and it is already the store for every other per-name kernel datum the *model* reads
      but the erasure registry does not itself compute (`ctorArities`, `ctorFields`,
      `casesDiscrPos`).

      **Coherence.** Nothing here forces `Γ.lparams n` to be `n`'s real `levelParams`;
      that is a fact about the walk, and it is stated where the walk is
      (`DeltaHyps.LparamsAgree`, keyed on the same `getConstInfo` fetch `decl_run`'s
      scope conjunct is keyed on). A `Γ` whose column lies makes the δ rule model a
      different unfolding, exactly as a `Γ` whose `ctorArities` lies makes `ctor_val`
      model a different saturation bound.

      Defaulted to `fun _ => []` — *universe-monomorphic everywhere* — so every existing
      `ErasureCtx` literal is byte-unchanged and, at that default,
      `body.instantiateLevelParams (Γ.lparams n) us` is `body` **definitionally**
      (`LeanToLambdaBox.instantiateLevelParams_nil`): the restated δ rule degenerates to
      the level-blind one it replaces. (Slice Γ-U4.) -/
  lparams : Name → List Name := fun _ => []

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
/-- The projection column is `withFixvars`-invariant, like every other registration
field. Landed `@[simp]` *with* the field rather than after it: the trap the three
lemmas above record — a `simp` at a block-local `Γ.withFixvars fv` leaving
`(Γ.withFixvars fv).projs` unreduced — is exactly what the bridge's motives walk into,
and `Erases.instFixvars`' `proj` arm is a `rfl` transport only because of this.
(Projection round, slice P0.) -/
@[simp] theorem ErasureCtx.withFixvars_projs (Γ : ErasureCtx) (fv : Name → Option FVarId) :
    (Γ.withFixvars fv).projs = Γ.projs := rfl

/-- The universe-parameter column is `withFixvars`-invariant too. Landed `@[simp]` with
the field, for the reason the `ctorArities`/`natPeano`/`inductives` trio records: the
bridge's motives run at a block-local `Γ.withFixvars fv`, and the δ rule now reads
`Γ.lparams` there. (Slice Γ-U4.) -/
@[simp] theorem ErasureCtx.withFixvars_lparams (Γ : ErasureCtx) (fv : Name → Option FVarId) :
    (Γ.withFixvars fv).lparams = Γ.lparams := rfl

/-! ### The `Γ`-in-motives coherence equation

The bridge induction's motives quantify their own `Γ` against a *fixed* ambient `Γ₀`, and
the only motion `visitMutual` ever performs on the context is `withFixvars` (the block
entry's `withReader … fixvars`; `lparams` lives in the reader, not in `Γ`). So the minimal
relation between a motive-local `Γ` and the ambient `Γ₀` is the single equation

```lean
    hΓ : Γ = Γ₀.withFixvars Γ.fixvars
```

— *every field but `fixvars` is `Γ₀`'s*. The two lemmas below are what make it usable: it
is `rfl` at the ambient instance (so every existing caller of the bridge instantiates it
with `withFixvars_self`), and `rfl` at a block-local one (`withFixvars_withFixvars` plus
`withFixvars_fixvars`). (Recursion wall, slice Γ-W0.) -/

/-- **Structure eta for the block-local context.** Reinstalling `Γ`'s own fixvar map is a
no-op — this is what makes the coherence equation `hΓ : Γ = Γ₀.withFixvars Γ.fixvars`
`rfl` at `Γ := Γ₀`. -/
@[simp] theorem ErasureCtx.withFixvars_self (Γ : ErasureCtx) :
    Γ.withFixvars Γ.fixvars = Γ := rfl

/-- **`withFixvars` is idempotent in its argument**: the second installation wins. With
`withFixvars_fixvars` this makes the coherence equation `rfl` at a *block-local*
`Γ := Γ₀.withFixvars fv` as well. -/
@[simp] theorem ErasureCtx.withFixvars_withFixvars (Γ : ErasureCtx)
    (fv fv' : Name → Option FVarId) :
    (Γ.withFixvars fv).withFixvars fv' = Γ.withFixvars fv' := rfl

namespace LeanToLambdaBox

/-- **Instantiating no parameters is the identity, definitionally.** `Lean.Expr`'s
`instantiateLevelParams` short-circuits on `paramNames.isEmpty || lvls.isEmpty`, and the
left disjunct reduces without looking at `lvls` — so this is `rfl`, at an arbitrary `us`.

This one equation is what makes slice Γ-U4 cheap. The δ rule (`SEvalDataι.delta`) and the
consistency premise (`SEnvConsistentL`) are restated at
`body.instantiateLevelParams (Γ.lparams n) us`; the column's default is `fun _ => []`; so
at every `ErasureCtx` the development actually builds, the restated forms *are* the old
ones and no discharge had to move. (The mirror equation
`e.instantiateLevelParams ps [] = e` is **not** `rfl` — `ps.isEmpty` blocks on a variable
`ps` — which is why the degeneracy is keyed on the parameter list and not on the call
site's levels.)

It lives here, beside the column, rather than beside either consumer: `SourceEvalData` and
`SubjectReductionFull` are siblings in the import graph and both need it. -/
@[simp] theorem instantiateLevelParams_nil {e : Expr} {us : List Level} :
    e.instantiateLevelParams [] us = e := rfl

end LeanToLambdaBox

/-- Convert a Lean `Name` to a `BinderName` exactly as `Erasure.fvar_to_name` does. -/
def nameToBinder (n : Name) : BinderName :=
  let s := n.toString
  if s.all (fun (c : Char) => decide (33 ≤ c.toNat ∧ c.toNat < 127)) then .named s else .anon
