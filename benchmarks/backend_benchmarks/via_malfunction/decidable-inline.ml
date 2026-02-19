(* To handle Lean's Decidable, here I think I need a datatype with a dummy field to match what the erasure will produce. *)
(* These implementations will probably be wrong if I erase irrelevant constructor args. *)
type decidable = IsFalse of Obj.t | IsTrue of Obj.t
let box = let rec f _ = Obj.repr f in Obj.repr f
let dec_of_bool b = if b then IsTrue box else IsFalse box
[@@inline always]

