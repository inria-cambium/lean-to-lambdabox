import LeanToLambdaBox.Basic

/-!
Operational semantics for λ_◻ terms.

This is verification scaffolding: definitions are written so that they typecheck
and pin down the intended meaning of `LBTerm` reduction, but the actual metatheory
(progress, preservation, confluence) is not proven here.

The design follows MetaRocq's `Erasure.EWcbvEval`:
* substitution is by de Bruijn index;
* `Step` is a small-step relation parameterised by the global environment of
  declarations produced by erasure;
* only the principal reduction rules and a minimal set of congruence rules are
  given — full congruence closure can be added when proofs are attempted.
-/

namespace LBTerm

/-- Look up a declaration in a `GlobalDeclarations` list. Linear scan; fine for the
    scaffolding, the list is logically a finite map. -/
def envLookup : GlobalDeclarations → Kername → Option GlobalDecl
  | [], _ => none
  | (k, d) :: rest, kn => if k.id == kn.id then some d else envLookup rest kn

/-- Shift de Bruijn indices ≥ `cutoff` up by `d`. -/
partial def shift (d cutoff : Nat) : LBTerm → LBTerm
  | bvar i => if i ≥ cutoff then bvar (i + d) else bvar i
  | lambda n b => lambda n (shift d (cutoff + 1) b)
  | letIn n v b => letIn n (shift d cutoff v) (shift d (cutoff + 1) b)
  | app f a => app (shift d cutoff f) (shift d cutoff a)
  | construct ind k args => construct ind k (args.map (shift d cutoff))
  | case info scr alts =>
    case info (shift d cutoff scr)
      (alts.map fun (ns, b) => (ns, shift d (cutoff + ns.length) b))
  | proj p e => proj p (shift d cutoff e)
  | fix defs i =>
    let m := defs.length
    fix (defs.map fun fd => { fd with body := shift d (cutoff + m) fd.body }) i
  | t => t  -- box, fvar, const, prim

/-- Substitute `s` for the bound variable at depth `d`, decrementing higher indices. -/
partial def subst (s : LBTerm) (d : Nat) : LBTerm → LBTerm
  | bvar i =>
    if i < d then bvar i
    else if i = d then shift d 0 s
    else bvar (i - 1)
  | lambda n b => lambda n (subst s (d + 1) b)
  | letIn n v b => letIn n (subst s d v) (subst s (d + 1) b)
  | app f a => app (subst s d f) (subst s d a)
  | construct ind k args => construct ind k (args.map (subst s d))
  | case info scr alts =>
    case info (subst s d scr)
      (alts.map fun (ns, b) => (ns, subst s (d + ns.length) b))
  | proj p e => proj p (subst s d e)
  | fix defs i =>
    let m := defs.length
    fix (defs.map fun fd => { fd with body := subst s (d + m) fd.body }) i
  | t => t

/-- Substitute the bvar 0 only. -/
@[inline] def subst1 (s : LBTerm) (t : LBTerm) : LBTerm := subst s 0 t

/--
Simultaneous substitution of `ss` for de Bruijn indices `0 .. ss.length - 1`.
Implemented by sequencing `subst1` applications: substituting `ss[0]` first
reduces every higher index by one, which is exactly what we want before
substituting `ss[1]` into position 0, and so on.
-/
def substList (ss : List LBTerm) (t : LBTerm) : LBTerm :=
  ss.foldl (fun acc s => subst1 s acc) t

/--
A handful of LBTerm shapes that don't reduce further on their own — useful
mostly as documentation; the `Step` relation does not require strict
call-by-value semantics here.
-/
def IsValue : LBTerm → Prop
  | box | lambda _ _ | construct _ _ _ | fix _ _ | prim _ | const _ | fvar _ => True
  | _ => False

/--
Small-step reduction relation for λ_◻, parameterised by a global environment
of declarations.

The constructors cover:
* `beta`  — β-reduction of applied lambdas
* `zeta`  — let-binding unfolding
* `iota`  — case analysis on a known constructor
* `delta` — constant unfolding from `Γ`
* `proj`  — projection from a known constructor
* `fix`   — fix unfolding when applied
* a minimal set of congruence rules under `app`, `letIn`, and `case`.

Additional congruence rules (e.g. under `construct`, `proj`, `fix`, plus the
two `letIn` arms not covered here) are left to be added when proofs are pursued.
-/
inductive Step (Γ : GlobalDeclarations) : LBTerm → LBTerm → Prop
  -- Principal reductions
  | beta (name : BinderName) (body arg : LBTerm) :
      Step Γ (app (lambda name body) arg) (subst1 arg body)
  | zeta (name : BinderName) (val body : LBTerm) :
      Step Γ (letIn name val body) (subst1 val body)
  | iota (info : InductiveId × Nat) (k : Nat) (args : List LBTerm)
         (alts : List (List BinderName × LBTerm))
         (names : List BinderName) (body : LBTerm)
         (h : alts[k]? = some (names, body)) :
      Step Γ (case info (construct info.1 k args) alts) (substList args body)
  | delta (kn : Kername) (body : LBTerm)
          (h : envLookup Γ kn = some (.constantDecl ⟨some body⟩)) :
      Step Γ (const kn) body
  | projRed (p : ProjectionInfo) (k : Nat) (args : List LBTerm) (v : LBTerm)
            (h : args[p.fieldIdx]? = some v) :
      Step Γ (proj p (construct p.indType k args)) v
  | fixUnfold (defs : List (@FixDef LBTerm)) (i : Nat) (arg : LBTerm)
              (def_i : @FixDef LBTerm) (h : defs[i]? = some def_i) :
      Step Γ (app (fix defs i) arg)
            (app (substList ((List.range defs.length).map (fun j => LBTerm.fix defs j)) def_i.body) arg)
  -- Selected congruence rules.
  | appLeft  {f f' a : LBTerm} (h : Step Γ f f')   : Step Γ (app f a) (app f' a)
  | appRight {f a a' : LBTerm} (h : Step Γ a a')   : Step Γ (app f a) (app f a')
  | letVal   {n v v' b : LBTerm} (h : Step Γ v v') : Step Γ (letIn (.named "_") v b) (letIn (.named "_") v' b)
  | caseDiscr {info s s' alts} (h : Step Γ s s')   : Step Γ (case info s alts) (case info s' alts)

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps (Γ : GlobalDeclarations) : LBTerm → LBTerm → Prop
  | refl  (t : LBTerm) : Steps Γ t t
  | step  {t u v : LBTerm} (h₁ : Step Γ t u) (h₂ : Steps Γ u v) : Steps Γ t v

end LBTerm
