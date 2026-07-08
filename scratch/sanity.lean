import LeanToLambdaBox.Erasure
open Erasure

-- Coverage: boxing (proof args), binders, lets, ctors (under/exactly/over-applied),
-- casesOn (incl. over-application), Nat literals (machine + peano), Int, recursion
-- (fix via visitMutual), mutual recursion, structures/projections, extern axioms.

def withProof (h : True) (n : Nat) : Nat := n
def constTrue : True := trivial
def useProof : Nat := withProof constTrue 42

structure Pair where
  fst : Nat
  snd : Bool

structure SVal where
  val : Nat
  prop : val = val   -- irrelevant field, exercises remove_irrel_constr_args

def mkPair (n : Nat) : Pair := ⟨n, true⟩
def getFst (p : Pair) : Nat := p.fst

def myLet (n : Nat) : Nat := let m := n; m

inductive Tree where
  | leaf
  | node (l r : Tree)

def Tree.size : Tree → Nat
  | .leaf => 1
  | .node l r => l.size + r.size

def underApplied : Tree → Tree := Tree.node .leaf   -- under-applied ctor (eta)

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

def caseOver (f : Bool → Nat) (b : Bool) : Nat :=
  (Bool.casesOn (motive := fun _ => Bool → Nat) b (fun _ => 1) (fun x => f x + 2)) b   -- over-applied casesOn

def intMatch (i : Int) : Int :=
  match i with
  | .ofNat n => Int.ofNat (n + 1)
  | .negSucc n => Int.negSucc n

def main1 : Nat := useProof + (mkPair 3).fst + getFst (mkPair 7) + myLet 5
def main2 : Nat := (underApplied .leaf).size + (if isEven 10 then 1 else 0) + caseOver (fun _ => 3) true
def main3 : Int := intMatch (-5) + intMatch 17

-- WS-O corpus extensions (2026-07-08): exercise exactly the surfaces the two
-- shipping edits touch.
-- (a) nondep-let: `have` desugars to `letE .. (nonDep := true)` — exercises the
--     `withLocalDef` `mkLetDecl` nd-drop edit.
def haveLet (n : Nat) : Nat := have m : Nat := n + 1; m + m
-- (b) universe-polymorphic constant whose body carries a level param: exercises
--     the `lparams := ci.levelParams` path in `visitMutual`/`isErasable`.
def upolyId.{u} {α : Sort u} (a : α) : α := a
def upolyMain : Nat := upolyId (upolyId 7) + upolyId 5
-- (c) mixed path: proof-typed *fvar* argument (`h : True`) passed alongside a
--     relevant `Nat` argument — oracle-true on a proper subterm + structural path.
def useProofFn (h : True) (n : Nat) : Nat := n

def main4 : Nat := haveLet 3
def main5 : Nat := upolyMain

#erase main1 to "scratch/sanity_out/main1.ast"
#erase main2 to "scratch/sanity_out/main2.ast"
#erase main3 to "scratch/sanity_out/main3.ast"
#erase main1 config { nat := .peano, extern := .preferLogical } to "scratch/sanity_out/main1_peano.ast"
#erase (SVal.mk 4 rfl).val config { remove_irrel_constr_args := true } to "scratch/sanity_out/sval_mask.ast"
#erase main4 to "scratch/sanity_out/main4_havelet.ast"
#erase main5 to "scratch/sanity_out/main5_upoly.ast"
#erase (fun (h : True) (n : Nat) => useProofFn h n) to "scratch/sanity_out/main6_prooffvar.ast"
