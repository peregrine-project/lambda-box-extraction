import FromLeanCommon.binarytrees
import FromLeanCommon.const_fold
import FromLeanCommon.deriv
import FromLeanCommon.qsort
import FromLeanCommon.qsort_single
import FromLeanCommon.qsort_fin
import FromLeanCommon.rbmap_beans
import FromLeanCommon.rbmap_std
import FromLeanCommon.rbmap_mono
import FromLeanCommon.rbmap_raw
import FromLeanCommon.unionfind
import FromLeanCommon.unionfind_noinline

/-
Test programs to be used with the "runonce" or "repeat" runners.
Since they don't depend on the argument Lean's closed term extraction must be deactivated to avoid adding startup overhead to everything.
Not really interesting for benchmarking I think.
-/
set_option compiler.extract_closed false in
def unit (_: Unit): Unit := .unit

set_option compiler.extract_closed false in
def demo0 (_: Unit): List Unit := [.unit, .unit, .unit]

set_option compiler.extract_closed false in
def demo1 (_: Unit): List Bool := List.replicate 5000 true |>.append <| List.replicate 3000 false

set_option compiler.extract_closed false in
def demo1_tc (_: Unit): List Bool := List.replicate 5000 true ++ List.replicate 3000 false

def repeat2 (x y: α) (n: Nat): List α :=
  match n with
  | 0 => []
  | n+1 => x :: y :: repeat2 x y n

set_option compiler.extract_closed false in
def demo2 (_: Unit) := List.map not (repeat2 true false 100)

set_option compiler.extract_closed false in
def demo3 (_: Unit) := and

set_option compiler.extract_closed false in
def cube (_: Unit) := 300^3

/-
Programs to be compiled with the "natio" runner, more interesting to benchmark.
-/

-- List.sum has a bug which causes the csimp List.foldr -> List.foldrTR not to apply, which leads to stack overflows.
-- https://github.com/leanprover/lean4/issues/7750
def list_sum_foldl n := List.replicate n 1 |>.foldl Nat.add 0

def list_sum_foldr n := List.replicate n 1 |>.foldr Nat.add 0

def list_sum_rev n := List.replicate n 1 |>.foldl Nat.add 0

def shared_list_sum_foldl n :=
  let l := List.replicate n 1
  let res := l.foldl Nat.add 0
  res + l[0]!

def shared_list_sum_foldr n :=
  let l := List.replicate n 1
  let res := l.foldr Nat.add 0
  res + l[0]!

def shared_list_sum_rev n :=
  let l := List.replicate n 1
  let res := l.reverse.foldl Nat.add 0
  res + l[0]!

def triangle_foldl (n: Nat) := List.range n |>.foldl Nat.add 0

def triangle_rec: Nat -> Nat
  | 0 => 0
  | n+1 => triangle_rec n + n

def triangle_acc_loop (acc: Nat): Nat -> Nat
  | 0 => acc
  | n+1 => triangle_acc_loop (n + acc) n

def triangle_acc := triangle_acc_loop 0

def iflazy (n: Nat): Nat := if n = 0 then 42 else iflazy (n-1)

mutual
def even: Nat -> Nat
  | 0 => 1
  | n+1 => odd n
def odd: Nat -> Nat
  | 0 => 0
  | n+1 => even n
end

-- Test whether Int.casesOn is implemented correctly (not for use as a benchmark).
-- add the line "intcases:natio" to TESTS to build.
/-
def intcases (n: Nat): Nat :=
  let i := Int.ofNat n
  match i - 10 with
  | .ofNat n => n
  | .negSucc n => n
-/
