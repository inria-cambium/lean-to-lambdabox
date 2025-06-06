import FromLeanCommon.binarytrees

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

-- currently List.sum is quadratic because it uses foldr without the csimp substitution.
-- List.replicate is also slow and stackoverflows, not sure why it's this exact power law.
def list_sum n := List.replicate n 1 |>.foldl Nat.add 0

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

#check ite
def iflazy (n: Nat): Nat := if n = 0 then 42 else iflazy (n-1)
