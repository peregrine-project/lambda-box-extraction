(* Implementation of Lean's Decidable to use when erasing irrelevant constructor args. *)
type decidable = IsFalse | IsTrue
let dec_of_bool b = if b then IsTrue else IsFalse
[@@inline always]
