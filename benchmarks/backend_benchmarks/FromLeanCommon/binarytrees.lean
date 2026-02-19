/-
Example binarytrees.lean from the Counting Bean tests, with some modifications:
- UInt32 has been replaced with Nat
- Async Tasks have been removed and replaced with synchronous operations
- I/O functions have been axiomatized and string literals removed
-/
namespace BinaryTrees

inductive Tree
  | nil
  | node (l r : Tree)
instance : Inhabited Tree := ⟨.nil⟩

-- This function has an extra argument to suppress the
-- common sub-expression elimination optimization
partial def make' (n d : Nat) : Tree :=
  if d = 0 then .node .nil .nil
  else .node (make' n (d - 1)) (make' (n + 1) (d - 1))

-- build a tree
def make (d : Nat) := make' d d

def check : Tree → Nat
  | .nil => 0
  | .node l r => 1 + check l + check r

def minN := 4

-- allocate and check lots of trees
partial def sumT (d i t : Nat) : Nat :=
  if i = 0 then t
  else
    let a := check (make d)
    sumT d (i-1) (t + a)

-- generate many trees
partial def depth (d m : Nat) : List (Nat × Nat × Nat) :=
  if d ≤ m then
    let n := 2 ^ (m - d + minN)
    (n, d, sumT d n 0) :: depth (d+2) m
  else []
end BinaryTrees

open BinaryTrees

def binarytrees (n: Nat): Nat :=
  -- let maxN := Nat.max (minN + 2) n
  let maxN := n
  let stretchN := maxN + 1

  -- stretch memory tree
  let c := check (make stretchN)
  -- out "stretch tree" stretchN c

  -- allocate a long lived tree
  let long := make maxN

  -- allocate, walk, and deallocate many bottom-up binary trees
  let vs := (depth minN maxN)  -- `using` (parList $ evalTuple3 r0 r0 rseq)
  -- vs.forM (fun (m, d, i) => out s!"{m}\t trees" d i.get)
  let v := vs.map (fun (m, d, i) => m + d + i) |>.foldl Nat.add 0

  -- confirm the long-lived binary tree still exists
  -- out "long lived tree" maxN (check long)
  let l := check long
  c + v + l
