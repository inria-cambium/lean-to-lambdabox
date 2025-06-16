import FromLeanCommon.binarytrees
import FromLeanCommon.rbmap

set_option linter.unusedVariables false

def demo0 (u: Unit): List Unit := [.unit, .unit, .unit]

-- TODO: The real Lean compiler performs csimp substitutions and replaces structurally recursive definitions of
-- common functions with tail-recursive implementations.
-- My erasure does not (yet) do this and probably this is bad for performance.
-- TODO: also test version using typeclass search to generate HAppend instance from "++" notation
def demo1 (u: Unit): List Bool := List.replicate 5000 true |>.append <| List.replicate 3000 false

def repeat2 (x y: α) (n: Nat): List α :=
  match n with
  | 0 => []
  | n+1 => x :: y :: repeat2 x y n

def demo2 (u: Unit) := List.map not (repeat2 true false 100)

def demo3 (u: Unit) := and

-- List.sum has a bug which causes the csimp List.foldr -> List.foldrTR not to apply, which leads to stack overflows.
-- https://github.com/leanprover/lean4/issues/7750
def list_sum n :=
  let l := List.replicate n 1
  let res := l.foldl Nat.add 0
  res + l[0]!

def list_sum_foldr n :=
  let l := List.replicate n 1
  let res := l.foldr Nat.add 0
  res + l[0]!

def list_sum_rev n :=
  let l := List.replicate n 1
  let res := l.reverse.foldl Nat.add 0
  res + l[0]!

def cube (u: Unit) := 300^3

def binarytrees: Nat -> Nat := BinaryTrees.main

def triangle (n: Nat) := List.range n |>.foldl Nat.add 0

def triangle_rec: Nat -> Nat
  | 0 => 0
  | n+1 => triangle_rec n + n

def triangle_acc_loop (acc n: Nat): Nat :=
  match n with
  | 0 => acc
  | n+1 => triangle_acc_loop (n + acc) n

def triangle_acc := triangle_acc_loop 0

def sub_3 (n: Nat): Nat :=
  n-3

def iflazy (n: Nat): Nat := if n = 0 then 42 else iflazy (n-1)

mutual
def even: Nat -> Nat
  | 0 => 1
  | n+1 => odd n
def odd: Nat -> Nat
  | 0 => 0
  | n+1 => even n
end
