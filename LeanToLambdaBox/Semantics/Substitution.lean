import LeanToLambdaBox.Basic

/-!
# de Bruijn substitution kit for λ□ terms

The environment lookup and the shift/substitution operations on `LBTerm`, shared
by every layer that reasons about λ□ reduction (`WcbvEval`, `LBOptimize`, the
`Erases` substitution lemmas, and the legacy small-step relation).

The conventions here **match lean4lean's `Expr.liftLooseBVars'`/`instantiate1'`**
(`shift d cutoff ≡ liftLooseBVars' · cutoff d`, `subst ≡ instantiate1'`), which is
what lets `erases_shift`/`erases_subst` line source and target up. Preserve them.
-/

/-- Structural boolean equality of module paths. `ModPath`/`Kername` derive only
    `Repr`/`Inhabited` in `Basic.lean`, so we supply the comparison locally (rather
    than editing the shared `Basic.lean`). -/
def ModPath.beq : ModPath → ModPath → Bool
  | .MPfile dp1, .MPfile dp2 => dp1 == dp2
  | .MPdot mp1 s1, .MPdot mp2 s2 => ModPath.beq mp1 mp2 && s1 == s2
  | _, _ => false

/-- Structural boolean equality of kernames — the **full** kername (modpath ×
    identifier), matching MetaRocq's `eq_kername`/`lookup_env` (which compare the
    whole kername, not just the identifier component). -/
def Kername.beq (k1 k2 : Kername) : Bool := k1.mp.beq k2.mp && k1.id == k2.id

namespace LBTerm

/-- Look up a declaration in a `GlobalDeclarations` list. Linear scan; fine for the
    scaffolding, the list is logically a finite map.

    Compares the **full** kername (modpath × id) via `Kername.beq`, matching
    MetaRocq's `lookup_env` (which uses `eq_kername`). -/
def envLookup : GlobalDeclarations → Kername → Option GlobalDecl
  | [], _ => none
  | (k, d) :: rest, kn => if Kername.beq k kn then some d else envLookup rest kn

/-! ### Shift / subst (mutual recursion with explicit list helpers).

We deliberately avoid `List.map` inside the principal recursive functions: the
structural-recursion checker cannot see through `map` for nested inductives,
so we factor the per-list traversals out into dedicated mutually-recursive
helpers. -/

mutual
/-- Shift de Bruijn indices ≥ `cutoff` up by `d`. -/
def shift (d cutoff : Nat) : LBTerm → LBTerm
  | bvar i => if i ≥ cutoff then bvar (i + d) else bvar i
  | lambda n b => lambda n (shift d (cutoff + 1) b)
  | letIn n v b => letIn n (shift d cutoff v) (shift d (cutoff + 1) b)
  | app f a => app (shift d cutoff f) (shift d cutoff a)
  | construct ind k args => construct ind k (shiftArgs d cutoff args)
  | case info scr alts => case info (shift d cutoff scr) (shiftAlts d cutoff alts)
  | proj p e => proj p (shift d cutoff e)
  | fix defs i => fix (shiftDefs d (cutoff + defs.length) defs) i
  | box => box
  | fvar x => fvar x
  | const k => const k
  | prim p => prim p

def shiftArgs (d cutoff : Nat) : List LBTerm → List LBTerm
  | [] => []
  | t :: rest => shift d cutoff t :: shiftArgs d cutoff rest

def shiftAlts (d cutoff : Nat) :
    List (List BinderName × LBTerm) → List (List BinderName × LBTerm)
  | [] => []
  | (ns, b) :: rest => (ns, shift d (cutoff + ns.length) b) :: shiftAlts d cutoff rest

def shiftDefs (d cutoff : Nat) : List (@FixDef LBTerm) → List (@FixDef LBTerm)
  | [] => []
  | fd :: rest => { fd with body := shift d cutoff fd.body } :: shiftDefs d cutoff rest
end

mutual
/-- Substitute `s` for the bound variable at depth `d`, decrementing higher indices. -/
def subst (s : LBTerm) (d : Nat) : LBTerm → LBTerm
  | bvar i =>
    if i < d then bvar i
    else if i = d then shift d 0 s
    else bvar (i - 1)
  | lambda n b => lambda n (subst s (d + 1) b)
  | letIn n v b => letIn n (subst s d v) (subst s (d + 1) b)
  | app f a => app (subst s d f) (subst s d a)
  | construct ind k args => construct ind k (substArgs s d args)
  | case info scr alts => case info (subst s d scr) (substAlts s d alts)
  | proj p e => proj p (subst s d e)
  | fix defs i => fix (substDefs s (d + defs.length) defs) i
  | box => box
  | fvar x => fvar x
  | const k => const k
  | prim p => prim p

def substArgs (s : LBTerm) (d : Nat) : List LBTerm → List LBTerm
  | [] => []
  | t :: rest => subst s d t :: substArgs s d rest

def substAlts (s : LBTerm) (d : Nat) :
    List (List BinderName × LBTerm) → List (List BinderName × LBTerm)
  | [] => []
  | (ns, b) :: rest => (ns, subst s (d + ns.length) b) :: substAlts s d rest

def substDefs (s : LBTerm) (d : Nat) : List (@FixDef LBTerm) → List (@FixDef LBTerm)
  | [] => []
  | fd :: rest => { fd with body := subst s d fd.body } :: substDefs s d rest
end

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

/-- Apply `f` to a list of arguments, left-to-right, building an application spine.
    `mkApps f [a₁, …, aₙ] = (…((f a₁) a₂)… aₙ)`. MetaRocq's `mkApps`; the shape of
    non-block constructor and applied-`fix` **values**. -/
def mkApps (f : LBTerm) : List LBTerm → LBTerm
  | [] => f
  | a :: rest => mkApps (app f a) rest

/-- The head of an application spine (peel every `.app`). MetaRocq `EAstUtils.head`.
    `spineHead (mkApps f args) = spineHead f`. -/
def spineHead : LBTerm → LBTerm
  | app f _ => spineHead f
  | t => t

/-- The argument list of an application spine (in order). `spineArgs (mkApps f args)
    = spineArgs f ++ args`; together with `spineHead` this recovers a spine's shape,
    giving `mkApps` injectivity for non-application heads. -/
def spineArgs : LBTerm → List LBTerm
  | app f a => spineArgs f ++ [a]
  | _ => []

@[simp] theorem mkApps_nil (f : LBTerm) : mkApps f [] = f := rfl

theorem mkApps_concat (f : LBTerm) (args : List LBTerm) (a : LBTerm) :
    mkApps f (args ++ [a]) = app (mkApps f args) a := by
  induction args generalizing f with
  | nil => rfl
  | cons x xs ih => simpa [mkApps] using ih (app f x)

theorem spineHead_mkApps (f : LBTerm) (args : List LBTerm) :
    spineHead (mkApps f args) = spineHead f := by
  induction args generalizing f with
  | nil => rfl
  | cons x xs ih => rw [mkApps, ih (app f x)]; rfl

theorem spineArgs_mkApps (f : LBTerm) (args : List LBTerm) :
    spineArgs (mkApps f args) = spineArgs f ++ args := by
  induction args generalizing f with
  | nil => simp
  | cons x xs ih =>
    rw [mkApps, ih (app f x)]
    simp [spineArgs]

@[simp] theorem spineHead_lambda (n : BinderName) (b : LBTerm) :
    spineHead (lambda n b) = lambda n b := rfl
@[simp] theorem spineHead_box : spineHead box = box := rfl
@[simp] theorem spineHead_construct (iid : InductiveId) (c : Nat) (args : List LBTerm) :
    spineHead (construct iid c args) = construct iid c args := rfl
@[simp] theorem spineArgs_construct (iid : InductiveId) (c : Nat) (args : List LBTerm) :
    spineArgs (construct iid c args) = [] := rfl
@[simp] theorem spineHead_fix (defs : List (@FixDef LBTerm)) (i : Nat) :
    spineHead (fix defs i) = fix defs i := rfl
@[simp] theorem spineArgs_fix (defs : List (@FixDef LBTerm)) (i : Nat) :
    spineArgs (fix defs i) = [] := rfl

/-- Injectivity of a constructor-headed application spine: the constructor and the
    argument list are recoverable. -/
theorem mkApps_construct_inj {iid iid' : InductiveId} {c c' : Nat}
    {args args' : List LBTerm}
    (h : mkApps (construct iid c []) args = mkApps (construct iid' c' []) args') :
    iid = iid' ∧ c = c' ∧ args = args' := by
  have ha : args = args' := by
    have := congrArg spineArgs h
    rwa [spineArgs_mkApps, spineArgs_mkApps, spineArgs_construct, spineArgs_construct,
      List.nil_append, List.nil_append] at this
  subst ha
  have := congrArg spineHead h
  rw [spineHead_mkApps, spineHead_mkApps, spineHead_construct, spineHead_construct] at this
  injection this with h1 h2 _
  exact ⟨h1, h2, rfl⟩

/-- Injectivity of a `fix`-headed application spine. -/
theorem mkApps_fix_inj {defs defs' : List (@FixDef LBTerm)} {i i' : Nat}
    {argsv argsv' : List LBTerm}
    (h : mkApps (fix defs i) argsv = mkApps (fix defs' i') argsv') :
    defs = defs' ∧ i = i' ∧ argsv = argsv' := by
  have ha : argsv = argsv' := by
    have := congrArg spineArgs h
    rwa [spineArgs_mkApps, spineArgs_mkApps, spineArgs_fix, spineArgs_fix,
      List.nil_append, List.nil_append] at this
  subst ha
  have := congrArg spineHead h
  rw [spineHead_mkApps, spineHead_mkApps, spineHead_fix, spineHead_fix] at this
  injection this with h1 h2
  exact ⟨h1, h2, rfl⟩

/-- A constructor-headed spine is never a `fix`-headed spine. -/
theorem mkApps_construct_ne_fix {iid : InductiveId} {c : Nat}
    {defs : List (@FixDef LBTerm)} {i : Nat} {args argsv : List LBTerm} :
    mkApps (construct iid c []) args ≠ mkApps (fix defs i) argsv := by
  intro h
  have := congrArg spineHead h
  rw [spineHead_mkApps, spineHead_mkApps, spineHead_construct, spineHead_fix] at this
  exact LBTerm.noConfusion this

/-- The fixpoint-unfolding substitution. MetaRocq
    `fix_subst l = [tFix l (n-1); …; tFix l 1; tFix l 0]` (with `n = |l|`), i.e.
    index `i ↦ tFix l (n-1-i)`. Used by `cunfold_fix`; only differs from the naïve
    `[tFix l 0; …; tFix l (n-1)]` for mutual blocks (`n ≥ 2`), but the order is
    load-bearing for correctness. -/
def fixSubst (defs : List (@FixDef LBTerm)) : List LBTerm :=
  (List.range defs.length).reverse.map (fun j => LBTerm.fix defs j)

end LBTerm
