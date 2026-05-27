import Lean
import LeanToLambdaBox.Basic

open Lean

/-!
A deeply embedded subset of Lean's `Expr` representing the fragment our erasure
function handles cleanly. This is the "source language" of the verified-erasure
statement — small enough to formalise, large enough to cover most non-extern,
non-`csimp` Lean code.

What's in:
  constants, bound/free variables, application, lambda, let,
  inductive constructors, `casesOn`, structural recursion via `fix`,
  a single `box` marker for irrelevant subterms (proofs, type formers)
  that the erasure relation can place in lieu of the original Lean expression.

What's deliberately out (and corresponds to the parts of `Erasure.lean` that are
not yet covered by the verification programme):
  dependent function types, `Prop`/`Type` sorts, metavariables, `mdata`,
  primitive literals, `@[extern]` axiomatised functions,
  `@[csimp]` rewriting, the machine-`Nat` lowering.

This file is verification scaffolding only. Definitions typecheck; metatheory
is left for the proof phase.
-/

namespace CExpr

inductive _root_.CExpr where
  /-- Marker for erased proof or type-former subterms. -/
  | box : CExpr
  | bvar : Nat → CExpr
  | fvar : FVarId → CExpr
  | const : Name → CExpr
  | app : CExpr → CExpr → CExpr
  | lam : Name → CExpr → CExpr
  | letE : Name → CExpr → CExpr → CExpr
  /-- `ctor typeName cidx args` — application of a constructor (parameters + fields
      collapsed into `args`, matching how erasure flattens construction). -/
  | ctor : Name → Nat → List CExpr → CExpr
  /-- `cases typeName discr alts` — case analysis on a value of the named
      inductive type. Each alt records its bound names and body. -/
  | cases : Name → CExpr → List (List Name × CExpr) → CExpr
  /-- Mutually recursive top-level fixpoints. -/
  | fix : List (Name × CExpr) → Nat → CExpr
deriving Inhabited

/-- Shift de Bruijn indices ≥ `cutoff` up by `d`. Mirrors `LBTerm.shift`. -/
partial def shift (d cutoff : Nat) : CExpr → CExpr
  | bvar i => if i ≥ cutoff then bvar (i + d) else bvar i
  | lam n b => lam n (shift d (cutoff + 1) b)
  | letE n v b => letE n (shift d cutoff v) (shift d (cutoff + 1) b)
  | app f a => app (shift d cutoff f) (shift d cutoff a)
  | ctor tn k args => ctor tn k (args.map (shift d cutoff))
  | cases tn scr alts =>
    cases tn (shift d cutoff scr)
      (alts.map fun (ns, b) => (ns, shift d (cutoff + ns.length) b))
  | fix defs i =>
    let m := defs.length
    fix (defs.map fun (n, b) => (n, shift d (cutoff + m) b)) i
  | t => t  -- box, fvar, const

partial def subst (s : CExpr) (d : Nat) : CExpr → CExpr
  | bvar i =>
    if i < d then bvar i
    else if i = d then shift d 0 s
    else bvar (i - 1)
  | lam n b => lam n (subst s (d + 1) b)
  | letE n v b => letE n (subst s d v) (subst s (d + 1) b)
  | app f a => app (subst s d f) (subst s d a)
  | ctor tn k args => ctor tn k (args.map (subst s d))
  | cases tn scr alts =>
    cases tn (subst s d scr)
      (alts.map fun (ns, b) => (ns, subst s (d + ns.length) b))
  | fix defs i =>
    let m := defs.length
    fix (defs.map fun (n, b) => (n, subst s (d + m) b)) i
  | t => t

@[inline] def subst1 (s : CExpr) (t : CExpr) : CExpr := subst s 0 t

def substList (ss : List CExpr) (t : CExpr) : CExpr :=
  ss.foldl (fun acc s => subst1 s acc) t

/--
Best-effort translation from Lean's `Expr` into `CExpr`. Returns `none` outside
the supported fragment.

Constructor / casesOn / structurally-recursive function references show up as
`.const` references in `Expr`; lifting them to `CExpr.ctor` / `.cases` / `.fix`
needs additional environment lookup and is deferred to the proof phase. Here we
only translate the "raw" subset.
-/
partial def ofExpr : Expr → Option CExpr
  | .bvar i => some (.bvar i)
  | .fvar id => some (.fvar id)
  | .const n _ => some (.const n)
  | .app f a => do
      let f' ← ofExpr f
      let a' ← ofExpr a
      return .app f' a'
  | .lam name _ body _ => do
      let b' ← ofExpr body
      return .lam name b'
  | .letE name _ val body _ => do
      let v' ← ofExpr val
      let b' ← ofExpr body
      return .letE name v' b'
  -- Unsupported in the verification subset:
  | .forallE .. | .sort .. | .mvar .. | .lit .. | .proj .. | .mdata .. => none

/--
Source-side environment: a partial map from constant names to their definitions.
Mirrors `GlobalDeclarations` on the `LBTerm` side.
-/
abbrev Env := Name → Option CExpr

/-- Small-step reduction for `CExpr`. The full congruence closure is elided. -/
inductive Step (Δ : Env) : CExpr → CExpr → Prop
  | beta (n : Name) (body arg : CExpr) :
      Step Δ (.app (.lam n body) arg) (subst1 arg body)
  | zeta (n : Name) (val body : CExpr) :
      Step Δ (.letE n val body) (subst1 val body)
  | iota (tn : Name) (k : Nat) (args : List CExpr)
         (alts : List (List Name × CExpr))
         (names : List Name) (body : CExpr)
         (h : alts[k]? = some (names, body)) :
      Step Δ (.cases tn (.ctor tn k args) alts) (substList args body)
  | delta (n : Name) (body : CExpr) (h : Δ n = some body) :
      Step Δ (.const n) body
  | fixUnfold (defs : List (Name × CExpr)) (i : Nat) (arg : CExpr)
              (def_i : Name × CExpr) (h : defs[i]? = some def_i) :
      Step Δ (.app (.fix defs i) arg)
            (.app (substList ((List.range defs.length).map (fun j => CExpr.fix defs j)) def_i.2) arg)
  -- Selected congruences
  | appLeft  {f f' a} (h : Step Δ f f')   : Step Δ (.app f a) (.app f' a)
  | appRight {f a a'} (h : Step Δ a a')   : Step Δ (.app f a) (.app f a')
  | casesDiscr {tn s s' alts} (h : Step Δ s s') :
      Step Δ (.cases tn s alts) (.cases tn s' alts)

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps (Δ : Env) : CExpr → CExpr → Prop
  | refl (t : CExpr) : Steps Δ t t
  | step {t u v : CExpr} (h₁ : Step Δ t u) (h₂ : Steps Δ u v) : Steps Δ t v

end CExpr
