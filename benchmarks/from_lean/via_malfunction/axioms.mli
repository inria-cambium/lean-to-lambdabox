(* From nat.mli *)
val def__Nat_add : Z.t -> Z.t -> Z.t
val def__Nat_sub : Z.t -> Z.t -> Z.t
val def__Nat_mul : Z.t -> Z.t -> Z.t
val def__Nat_div : Z.t -> Z.t -> Z.t
val def__Nat_mod : Z.t -> Z.t -> Z.t
val def__Nat_beq : Z.t -> Z.t -> bool
val def__Nat_ble : Z.t -> Z.t -> bool

val def__Nat_decEq : Z.t -> Z.t -> Decidable.decidable
val def__Nat_decLe : Z.t -> Z.t -> Decidable.decidable
val def__Nat_decLt : Z.t -> Z.t -> Decidable.decidable

val def__Nat_land : Z.t -> Z.t -> Z.t
val def__Nat_lor : Z.t -> Z.t -> Z.t
val def__Nat_lxor : Z.t -> Z.t -> Z.t
val def__Nat_shiftl : Z.t -> int -> Z.t
val def__Nat_shiftr : Z.t -> int -> Z.t
val def__Nat_pow : Z.t -> int -> Z.t
val def__Nat_gcd : Z.t -> Z.t -> Z.t
val def__Nat_log2 : Z.t -> int
val def__Nat_pred : Z.t -> Z.t

(* From int.mli *)
val def__Int_ofNat: Z.t -> Z.t
val def__Int_neg: Z.t -> Z.t
val def__Int_neg_succ_of_nat: Z.t -> Z.t
val def__Int_add: Z.t -> Z.t -> Z.t
val def__Int_ediv: Z.t -> Z.t -> Z.t
val def__Int_emod: Z.t -> Z.t -> Z.t
val def__Int_beq : Z.t -> Z.t -> bool
val def__Int_ble : Z.t -> Z.t -> bool
val def__Int_decEq : Z.t -> Z.t -> Decidable.decidable
val def__Int_decLe : Z.t -> Z.t -> Decidable.decidable
val def__Int_mul : Z.t -> Z.t -> Z.t

(* From eq.mli *)
val def__Eq_rec: Obj.t -> Obj.t -> Obj.t -> 'a -> Obj.t -> Obj.t -> 'a
