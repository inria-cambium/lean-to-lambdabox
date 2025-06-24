type decidable = IsFalse of Obj.t | IsTrue of Obj.t
val dec_of_bool: bool -> decidable
