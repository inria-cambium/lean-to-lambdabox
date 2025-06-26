let def__Int_ofNat (n: Z.t) = n
[@@ inline always]

let def__Int_neg n = (Z.neg [@inlined]) n
[@@ inline always]

let def__Int_neg_succ_of_nat n = (Z.neg [@inlined]) ((Z.succ [@inlined]) n)
[@@ inline always]

let def__Int_add n m = (Z.add [@inlined]) n m
[@@ inline always]

let def__Int_ediv n m = if Z.equal m Z.zero then Z.zero else (Z.ediv [@inlined]) n m
[@@ inline always]

let def__Int_emod n m = if Z.equal m Z.zero then n else (Z.erem [@inlined]) n m
[@@ inline always]

let def__Int_beq x y = Z.equal x y
[@@inline always]

let def__Int_ble x y = (Z.leq [@inlined]) x y
[@@inline always]

let def__Int_decEq n m = Decidable.dec_of_bool @@ def__Int_beq n m
[@@inline always]

let def__Int_decLe n m = Decidable.dec_of_bool @@ def__Int_ble n m
[@@inline always]

let def__Int_mul n m = (Z.mul [@inlined]) n m
[@@ inline always]

