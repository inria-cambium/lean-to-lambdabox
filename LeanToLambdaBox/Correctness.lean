import LeanToLambdaBox.Basic
import LeanToLambdaBox.Semantics
import LeanToLambdaBox.CExpr

/-!
Erasure correctness — statement only.

This file defines the relation `Erases : CExpr → LBTerm → Prop` that mirrors
what the erasure function in `Erasure.lean` computes, and states the
preservation theorem connecting source-side reduction to target-side
reduction.

Proofs are deferred (`sorry`). The point of this file is to commit to a
precise, typechecked statement of what "verified erasure" means in this
project, so that progress on the proof can proceed file-by-file (see
Phase 3 of `attack-plan` for the staged plan).
-/

open Lean

/--
Context relating source-side names to target-side identifiers. The erasure
function in `Erasure.lean` builds this implicitly via `register_inductive` and
the `constants`/`inductives` fields of `ErasureState`; here we abstract it as
a parameter so that the `Erases` relation does not need to traverse the global
environment.
-/
structure ErasureCtx where
  /-- For each source inductive type name, the corresponding InductiveId. -/
  inductives : Name → Option InductiveId
  /-- For each source constant, the kername it is bound to on the target side. -/
  constants  : Name → Kername
  /-- For each source *constructor* name, its `(InductiveId, constructor index)`
      as `register_inductive` assigns it. Used by the real-`Expr` `Erases`
      (`LeanToLambdaBox.Erases`) to recognise constructor applications; the legacy
      `CExpr`-based `Erases` does not reference it. -/
  ctors : Name → Option (InductiveId × Nat) := fun _ => none

/-- Helper: convert a Lean `Name` to a `BinderName` exactly as `Erasure.fvar_to_name` does. -/
def nameToBinder (n : Name) : BinderName :=
  let s := n.toString
  if s.all (fun (c : Char) => decide (33 ≤ c.toNat ∧ c.toNat < 127)) then .named s else .anon

/--
Inductive specification of the erasure function.

Each constructor corresponds to one branch of `Erasure.visitExpr`. The
`Erases` relation deliberately does *not* model:
  * `Prop`/`Type` distinctions (box is just allowed everywhere)
  * `csimp` rewrites or `@[extern]` axiom swaps
  * the machine-`Nat` lowering
For these the verified subset is silent — the practical pipeline goes
through additional, unverified rewrites layered on top.
-/
inductive Erases (Γ : ErasureCtx) : CExpr → LBTerm → Prop
  /-- Irrelevant subterms erase to box. -/
  | box : Erases Γ .box .box
  /-- Bound variables. -/
  | bvar (i : Nat) : Erases Γ (.bvar i) (.bvar i)
  /-- Free variables. -/
  | fvar (x : FVarId) : Erases Γ (.fvar x) (.fvar x)
  /-- Constants are looked up in the erasure context. -/
  | const (n : Name) (kn : Kername) (h : Γ.constants n = kn) :
      Erases Γ (.const n) (.const kn)
  /-- Application. -/
  | app {f f' a a'} (hf : Erases Γ f f') (ha : Erases Γ a a') :
      Erases Γ (.app f a) (.app f' a')
  /-- Lambda. -/
  | lam (n : Name) {b b'} (hb : Erases Γ b b') :
      Erases Γ (.lam n b) (.lambda (nameToBinder n) b')
  /-- Let-binding. -/
  | letE (n : Name) {v v' b b'} (hv : Erases Γ v v') (hb : Erases Γ b b') :
      Erases Γ (.letE n v b) (.letIn (nameToBinder n) v' b')
  /-- Constructor application. -/
  | ctor (tn : Name) (k : Nat) (iid : InductiveId)
         {args : List CExpr} {args' : List LBTerm}
         (hi  : Γ.inductives tn = some iid)
         (hl  : args.length = args'.length)
         (hes : ∀ i (h : i < args.length),
                  Erases Γ args[i] (args'[i]'(hl ▸ h))) :
      Erases Γ (.ctor tn k args) (.construct iid k args')
  /-- Case analysis. -/
  | cases (tn : Name) (iid : InductiveId) (numParams : Nat)
          {discr discr'} {alts : List (List Name × CExpr)}
          {alts' : List (List BinderName × LBTerm)}
          (hi  : Γ.inductives tn = some iid)
          (hd  : Erases Γ discr discr')
          (hl  : alts.length = alts'.length)
          (hns : ∀ i (h : i < alts.length),
                   alts[i].1.length = (alts'[i]'(hl ▸ h)).1.length)
          (hes : ∀ i (h : i < alts.length),
                   Erases Γ alts[i].2 (alts'[i]'(hl ▸ h)).2) :
      Erases Γ (.cases tn discr alts) (.case (iid, numParams) discr' alts')
  /-- Mutually recursive fix. -/
  | fix {defs : List (Name × CExpr)} {defs' : List (@FixDef LBTerm)} (i : Nat)
        (hl  : defs.length = defs'.length)
        (hes : ∀ j (h : j < defs.length),
                 Erases Γ defs[j].2 (defs'[j]'(hl ▸ h)).body) :
      Erases Γ (.fix defs i) (.fix defs' i)

/--
Consistency between source-side and target-side global environments.

For every constant `n` with body `b` on the source side, the target environment
contains a binding from `Γ.constants n` to some `b'` such that `Erases Γ b b'`.
-/
def EnvConsistent (Γ : ErasureCtx) (Δ : CExpr.Env) (E : GlobalDeclarations) : Prop :=
  ∀ n b, Δ n = some b →
    ∃ b', LBTerm.envLookup E (Γ.constants n) = some (.constantDecl ⟨some b'⟩)
        ∧ Erases Γ b b'

/-
**Erasure preservation** — the top-level statement is proved as
`ErasureProofs.Irrel.preservation_irrel` (see `Proofs/Irrel.lean`) and
re-exported with this name as `erase_preservation` from the library root
`LeanToLambdaBox.lean`.

`Correctness.lean` cannot host the proof directly because the staged
proofs in `Proofs/{Lambda,Constants,Inductives,Fix,Irrel}.lean` import
`Correctness.lean`; the dependency cycle is broken by putting the final
wrapper above `Irrel.lean`.

If a source term `e` erases to target term `t` under context `Γ` with
consistent global environments, and `e` takes one source-level reduction step
to `e'`, then `t` reduces in zero or more target-level steps to some `t'`
that erases `e'`.

Proof structure: Lambda → Constants → Inductives → Fix → Irrel.
-/
