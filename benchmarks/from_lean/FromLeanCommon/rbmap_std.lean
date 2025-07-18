import Lean.Data.RBMap

namespace RBMapStd

-- Unsure why this isn't already defined somewhere.
def cmp (n m : Nat) : Ordering :=
  bif n.blt m then .lt
  else bif m.blt n then .gt
  else .eq

abbrev Tree := Lean.RBMap Nat Bool cmp

def mkMapAux : Nat → Tree → Tree
  | 0,   m => m
  | n+1, m => mkMapAux n (Lean.RBMap.insert m n (n % 10 = 0))

def mkMap (n : Nat) :=
  mkMapAux n Lean.RBMap.empty

end RBMapStd

def rbmap_std (n: Nat): Nat :=
  let m := RBMapStd.mkMap n
  let v := m.fold (fun r _ v => if v then r + 1 else r) 0
  v
