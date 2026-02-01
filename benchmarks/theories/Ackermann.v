(** * Ackermann Function Benchmark

    The Ackermann function is a classic example of a total computable function
    that is not primitive recursive. It grows extremely fast.

    A(0, n) = n + 1
    A(m, 0) = A(m-1, 1)
    A(m, n) = A(m-1, A(m, n-1))

    Uses nat for simplicity (values grow too fast for fixed-width integers).
*)

From Stdlib Require Import Arith.

(** Ackermann function with explicit fuel for termination *)
Fixpoint ackermann_fuel (fuel : nat) (m n : nat) : nat :=
  match fuel with
  | O => 0  (* Out of fuel *)
  | S fuel' =>
      match m with
      | O => S n
      | S m' =>
          match n with
          | O => ackermann_fuel fuel' m' 1
          | S n' => ackermann_fuel fuel' m' (ackermann_fuel fuel' m n')
          end
      end
  end.

(** Ackermann with sufficient fuel *)
Definition ackermann (m n : nat) : nat :=
  ackermann_fuel (Nat.pow 2 20) m n.

(** Test values:
    A(0, 0) = 1
    A(1, 1) = 3
    A(2, 2) = 7
    A(3, 3) = 61
    A(3, 4) = 125
    A(3, 9) = 4093
*)
Definition test_ack_0_0 : nat := ackermann 0 0.  (* 1 *)
Definition test_ack_1_1 : nat := ackermann 1 1.  (* 3 *)
Definition test_ack_2_2 : nat := ackermann 2 2.  (* 7 *)
Definition test_ack_3_3 : nat := ackermann 3 3.  (* 61 *)
Definition test_ack_3_9 : nat := ackermann 3 9.  (* 4093 *)

(** Benchmark: A(3, 10) = 8189 *)
Definition ackermann_bench : nat := ackermann 3 10.
