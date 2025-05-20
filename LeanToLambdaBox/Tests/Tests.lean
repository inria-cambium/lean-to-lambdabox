namespace Tests

set_option linter.unusedVariables false

def demo0 (u: Unit): List Unit := [.unit, .unit, .unit]

-- TODO: The real Lean compiler performs csimp substitutions and replaces structurally recursive definitions of
-- common functions with tail-recursive implementations.
-- My erasure does not do this and probably this is bad for performance.
def demo1 (u: Unit): List Bool := List.replicate 50 true |>.append <| List.replicate 50 false
/-
set_option pp.all true
#print demo1
-/

def repeat2 (x y: α) (n: Nat): List α :=
  match n with
  | 0 => []
  | n+1 => x :: y :: repeat2 x y n

def demo2 (u: Unit) := List.map not (repeat2 true false 100)

def demo3 (u: Unit) := and

def list_sum (u: Unit) := List.replicate 100 1 |>.foldl Nat.add 0

end Tests
