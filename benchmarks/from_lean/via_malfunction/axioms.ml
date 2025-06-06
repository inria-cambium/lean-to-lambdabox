(* Definitions used to implement Lean definitions without a body (including axioms), and @[extern] functions with a body if config.extern is .preferAxiom . *)

(* Use Zarith for operations on Nat. *)
let def__Nat_add = Z.add
let def__Nat_sub n m = if Z.(n <= m) then Z.zero else Z.sub n m (* Saturating subtraction on natural numbers. *)
let def__Nat_mul = Z.mul
let def__Nat_div n m = if Z.Compare.(m = Z.zero) then Z.zero else Z.ediv n m (* In Lean, division by zero returns zero. *)
(* let def__Nat_div_exact = _ (* Depends on whether the proof argument is removed or not. *) *)
let def__Nat_mod n m = if Z.Compare.(m = Z.zero) then n else Z.erem n m
let def__Nat_beq = Z.equal
let def__Nat_ble = Z.leq

(* To handle Lean's Decidable, here I think I need a datatype with a dummy field to match what the erasure will produce. *)
let box = let rec f _ = Obj.repr f in Obj.repr f
type decidable = IsTrue of Obj.t | IsFalse of Obj.t
let dec_of_bool b = if b then IsTrue box else IsFalse box
(* These implementations will probably be wrong if I erase irrelevant constructor args. *)
let def__Nat_decEq n m = dec_of_bool @@ def__Nat_beq n m
let def__Nat_decLe n m = dec_of_bool @@ def__Nat_ble n m
let def__Nat_decLt n m = dec_of_bool @@ Z.Compare.(n < m)

let def__Nat_land = Z.logand
let def__Nat_lor = Z.logor
let def__Nat_lxor = Z.logxor
let def__Nat_shiftl = Z.shift_left (* Zarith expects the second argument to be of type int and not Z.t, so if doing nonsense this might give garbage results. *)
let def__Nat_shiftr = Z.shift_right (* See above. *)

let def__Nat_pow = Z.pow
let def__Nat_gcd = Z.gcd
let def__Nat_log2 n = if Z.Compare.(n = Z.zero) then 0 else Z.log2 n

let def__Nat_pred n = def__Nat_sub n Z.one
