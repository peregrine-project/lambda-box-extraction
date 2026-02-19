/- Removed printing and switched to using the regular Array.qsort. -/

namespace QsortSingle

abbrev Elem := Nat

def badRand (seed : Elem) : Elem :=
(seed * 1664525 + 1013904223) % UInt32.size

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

end QsortSingle
open QsortSingle

def qsort_single (n: Nat): Nat :=
  let xs := mkRandomArray n n Array.empty
  let xs := Array.qsort xs (fun a b => a < b)
  checkSortedAux xs 0
