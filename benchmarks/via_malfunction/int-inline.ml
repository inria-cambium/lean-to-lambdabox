let def__Int_ofNat (n: Z.t) = n
[@@ inline always]

let def__Int_neg n = (Z.neg [@inlined hint]) n
[@@ inline always]

let def__Int_negSucc n = (Z.neg [@inlined hint]) ((Z.succ [@inlined hint]) n)
[@@ inline always]

let def__Int_add n m = (Z.add [@inlined hint]) n m
[@@ inline always]

let def__Int_sub n m = (Z.sub [@inlined hint]) n m
[@@ inline always]

let def__Int_ediv n m = if Z.equal m Z.zero then Z.zero else (Z.ediv [@inlined hint]) n m
[@@ inline always]

let def__Int_emod n m = if Z.equal m Z.zero then n else (Z.erem [@inlined hint]) n m
[@@ inline always]

let def__Int_decEq n m = Decidable.dec_of_bool @@ Z.equal n m
[@@inline always]

let def__Int_decLe n m = Decidable.dec_of_bool @@ (Z.leq [@inlined hint]) n m
[@@inline always]

let def__Int_mul n m = (Z.mul [@inlined hint]) n m
[@@ inline always]

