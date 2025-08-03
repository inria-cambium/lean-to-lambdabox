let def__Int_ofNat n = n

let def__Int_neg = Z.neg

let def__Int_negSucc n = Z.neg (Z.succ n)

let def__Int_add = Z.add

let def__Int_ediv n m = if Z.equal m Z.zero then Z.zero else Z.ediv n m

let def__Int_emod n m = if Z.equal m Z.zero then n else Z.erem n m

let def__Int_beq = Z.equal

let def__Int_ble = Z.leq

let def__Int_decEq n m = Decidable.dec_of_bool @@ def__Int_beq n m

let def__Int_decLe n m = Decidable.dec_of_bool @@ def__Int_ble n m

let def__Int_mul = Z.mul

