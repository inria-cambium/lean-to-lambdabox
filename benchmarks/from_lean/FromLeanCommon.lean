import FromLeanCommon.binarytrees
import FromLeanCommon.const_fold
import FromLeanCommon.deriv
import FromLeanCommon.qsort
import FromLeanCommon.qsort_single
import FromLeanCommon.qsort_fin
import FromLeanCommon.rbmap_beans
import FromLeanCommon.rbmap_std
import FromLeanCommon.rbmap_mono
import FromLeanCommon.rbmap_raw
import FromLeanCommon.unionfind

def unit (_: Unit): Unit := .unit

def demo0 (_: Unit): List Unit := [.unit, .unit, .unit]

def demo1 (_: Unit): List Bool := List.replicate 5000 true |>.append <| List.replicate 3000 false

def demo1_tc (_: Unit): List Bool := List.replicate 5000 true ++ List.replicate 3000 false

def repeat2 (x y: α) (n: Nat): List α :=
  match n with
  | 0 => []
  | n+1 => x :: y :: repeat2 x y n

def demo2 (_: Unit) := List.map not (repeat2 true false 100)

def demo3 (_: Unit) := and

-- List.sum has a bug which causes the csimp List.foldr -> List.foldrTR not to apply, which leads to stack overflows.
-- https://github.com/leanprover/lean4/issues/7750
def list_sum_foldl n := List.replicate n 1 |>.foldl Nat.add 0

def list_sum_foldr n := List.replicate n 1 |>.foldr Nat.add 0

def list_sum_rev n := List.replicate n 1 |>.foldl Nat.add 0

def shared_list_sum_foldl n :=
  let l := List.replicate n 1
  let res := l.foldl Nat.add 0
  res + l[0]!

def shared_list_sum_foldr n :=
  let l := List.replicate n 1
  let res := l.foldr Nat.add 0
  res + l[0]!

def shared_list_sum_rev n :=
  let l := List.replicate n 1
  let res := l.reverse.foldl Nat.add 0
  res + l[0]!

def cube (_: Unit) := 300^3

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
