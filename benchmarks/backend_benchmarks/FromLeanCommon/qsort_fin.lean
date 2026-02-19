/- A version of the qsort benchmark operating on `Fin n` to test pruning and unboxing. -/

namespace QsortFin

abbrev Elem := Fin UInt32.size

def badRand (seed : Elem) : Elem :=
  -- Using the default ofNat instance for Fin inserts a runtime modulo operation silently.
  -- Recall that operations on Fin n are performed modulo n, so this is the same as the version with raw `Nat`s.
  seed * ⟨1664525, by unfold UInt32.size; omega⟩ + ⟨1013904223, by unfold UInt32.size; omega⟩  

def mkRandomArray : Nat → Elem → Array Elem → Array Elem
| 0,   _, as => as
| i+1, seed, as => mkRandomArray i (badRand seed) (as.push seed)

-- return 0 if sorted and 1 if not
partial def checkSortedAux (a : Array Elem) : Nat → Nat
| i =>
  if i < a.size - 1 then
    if a[i]! <= a[i+1]! then checkSortedAux a (i+1) else 1
  else
    0

end QsortFin
open QsortFin

def qsort_fin (n: Nat): Nat :=
  List.range n
  |>.map (fun i =>
    let xs := mkRandomArray i (Fin.ofNat _ i) Array.empty
    let xs := Array.qsort xs (fun a b => a < b)
    checkSortedAux xs 0)
  |>.foldl Nat.add 0
