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

-- TODO: currently big Nat literals crash the extraction since we're counting in unary.
def list_sum (u: Unit) := List.replicate 10_000_000 1 |>.foldl Nat.add 0

def cube (u: Unit) := 300^3
