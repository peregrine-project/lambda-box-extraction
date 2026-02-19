(* Use Zarith for operations on Nat. *)
(* Everything eligible is annotated to be inlined by the OCaml compiler. Some functions such as Z.equal are directly defined as `external` in OCaml and cannot be inlined. *)
let def__Nat_add x y = (Z.add [@inlined]) x y
[@@inline always]

let def__Nat_sub n m = if (Z.leq [@inlined]) n m then Z.zero else (Z.sub [@inlined]) n m (* Saturating subtraction on natural numbers. *)
[@@inline always]

let def__Nat_mul x y = (Z.mul [@inlined]) x y
[@@inline always]

let def__Nat_div n m = if Z.equal m Z.zero then Z.zero else (Z.ediv [@inlined]) n m (* In Lean, division by zero returns zero. *)
[@@inline always]

(* let def__Nat_div_exact = _ (* Depends on whether the proof argument is removed or not. *) *)
let def__Nat_mod n m = if Z.equal m Z.zero then n else (Z.erem [@inlined]) n m
[@@inline always]

let def__Nat_beq x y = Z.equal x y
[@@inline always]

let def__Nat_ble x y = (Z.leq [@inlined]) x y
[@@inline always]

let def__Nat_decEq n m = Decidable.dec_of_bool @@ def__Nat_beq n m
[@@inline always]

let def__Nat_decLe n m = Decidable.dec_of_bool @@ def__Nat_ble n m
[@@inline always]

let def__Nat_decLt n m = Decidable.dec_of_bool @@ (Z.lt [@inlined]) n m
[@@inline always]

let def__Nat_land x y = (Z.logand [@inlined]) x y
[@@inline always]

let def__Nat_lor x y = (Z.logor [@inlined]) x y
[@@inline always]

let def__Nat_lxor x y = (Z.logxor [@inlined]) x y
[@@inline always]

let def__Nat_shiftl x y = (Z.shift_left [@inlined]) x y (* Zarith expects the second argument to be of type int and not Z.t, so if doing nonsense this might give garbage results. *)
[@@inline always]

let def__Nat_shiftr x y = (Z.shift_right [@inlined]) x y (* See above. *)
[@@inline always]

let def__Nat_pow x y = Z.pow x y
[@@inline always]

let def__Nat_gcd x y = Z.gcd x y
[@@inline always]

let def__Nat_log2 n = if Z.equal n Z.zero then 0 else (Z.log2 [@inlined]) n
[@@inline always]

let def__Nat_pred n = (Z.pred [@inlined]) n
[@@inline always]
