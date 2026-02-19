/-
This is rbmap_std with the code specialized for maps Nat -> Bool. Maps still carry the invariant.
-/

namespace RBMapMono

inductive RBColor where
  | red | black

inductive RBNode where
  | leaf                                                                                        : RBNode
  | node  (color : RBColor) (lchild : RBNode) (key : Nat) (val : Bool) (rchild : RBNode) : RBNode

namespace RBNode
variable {α : Type u} {β : α → Type v} {σ : Type w}

open RBColor Nat

-- @[specialize] def fold (f : σ → (k : α) → β k → σ) : (init : σ) → RBNode → σ
def fold (f : σ → Nat → Bool → σ) : (init : σ) → RBNode → σ
  | b, leaf           => b
  | b, node _ l k v r => fold f (f (fold f b l) k v) r

-- the first half of Okasaki's `balance`, concerning red-red sequences in the left child
@[inline] def balance1 : RBNode → Nat → Bool → RBNode → RBNode
  | node red (node red a kx vx b) ky vy c, kz, vz, d
  | node red a kx vx (node red b ky vy c), kz, vz, d => node red (node black a kx vx b) ky vy (node black c kz vz d)
  | a,                                     kx, vx, b => node black a kx vx b

-- the second half, concerning red-red sequences in the right child
@[inline] def balance2 : RBNode → Nat → Bool → RBNode → RBNode
  | a, kx, vx, node red (node red b ky vy c) kz vz d
  | a, kx, vx, node red b ky vy (node red c kz vz d) => node red (node black a kx vx b) ky vy (node black c kz vz d)
  | a, kx, vx, b                                     => node black a kx vx b

def isRed : RBNode → Bool
  | node red .. => true
  | _           => false

def isBlack : RBNode → Bool
  | node black .. => true
  | _             => false

def cmp (n m : Nat) : Ordering :=
  bif n.blt m then .lt
  else bif m.blt n then .gt
  else .eq

section Insert

def ins : RBNode → Nat → Bool → RBNode
  | leaf,               kx, vx => node red leaf kx vx leaf
  | node red a ky vy b, kx, vx =>
    match cmp kx ky with
    | Ordering.lt => node red (ins a kx vx) ky vy b
    | Ordering.gt => node red a ky vy (ins b kx vx)
    | Ordering.eq => node red a kx vx b
  | node black a ky vy b, kx, vx =>
    match cmp kx ky with
    | Ordering.lt => balance1 (ins a kx vx) ky vy b
    | Ordering.gt => balance2 a ky vy (ins b kx vx)
    | Ordering.eq => node black a kx vx b

def setBlack : RBNode → RBNode
  | node _ l k v r => node black l k v r
  | e              => e

def insert (t : RBNode) (k : Nat) (v : Bool) : RBNode :=
  if isRed t then setBlack (ins t k v)
  else ins t k v

end Insert

def setRed : RBNode → RBNode
  | node _ a k v b => node red a k v b
  | e              => e

def balLeft : RBNode → Nat → Bool → RBNode → RBNode
  | node red a kx vx b,   k, v, r                    => node red (node black a kx vx b) k v r
  | l, k, v, node black a ky vy b                    => balance2 l k v (node red a ky vy b)
  | l, k, v, node red (node black a ky vy b) kz vz c => node red (node black l k v a) ky vy (balance2 b kz vz (setRed c))
  | l, k, v, r                                       => node red l k v r -- unreachable

def balRight (l : RBNode) (k : Nat) (v : Bool) (r : RBNode) : RBNode :=
  match r with
  | (node red b ky vy c) => node red l k v (node black b ky vy c)
  | _ => match l with
    | node black a kx vx b                    => balance1 (node red a kx vx b) k v r
    | node red a kx vx (node black b ky vy c) => node red (balance1 (setRed a) kx vx b) ky vy (node black c k v r)
    | _                                       => node red l k v r -- unreachable

/-- The number of nodes in the tree. -/
@[local simp] def size : RBNode → Nat
  | leaf => 0
  | node _ x _ _ y => x.size + y.size + 1

def appendTrees :  RBNode → RBNode → RBNode
  | leaf, x => x
  | x, leaf => x
  | node red a kx vx b,   node red c ky vy d   =>
    match appendTrees b c with
    | node red b' kz vz c' => node red (node red a kx vx b') kz vz (node red c' ky vy d)
    | bc                   => node red a kx vx (node red bc ky vy d)
  | node black a kx vx b,   node black c ky vy d   =>
     match appendTrees b c with
     | node red b' kz vz c' => node red (node black a kx vx b') kz vz (node black c' ky vy d)
     | bc                   => balLeft a kx vx (node black bc ky vy d)
   | a, node red b kx vx c   => node red (appendTrees a b) kx vx c
   | node red a kx vx b,   c => node red a kx vx (appendTrees b c)
termination_by x y => x.size + y.size

section Erase

@[specialize] def del (x : Nat) : RBNode → RBNode
  | leaf           => leaf
  | node _ a y v b =>
    match cmp x y with
    | Ordering.lt =>
      if a.isBlack then balLeft (del x a) y v b
      else node red (del x a) y v b
    | Ordering.gt =>
      if b.isBlack then balRight a y v (del x b)
      else node red a y v (del x b)
    | Ordering.eq => appendTrees a b

@[specialize] def erase (x : Nat) (t : RBNode) : RBNode :=
  let t := del x t;
  t.setBlack

end Erase

inductive WellFormed : RBNode → Prop where
  | leafWff : WellFormed leaf
  | insertWff {n n' : RBNode} {k : Nat} {v : Bool} : WellFormed n → n' = insert n k v → WellFormed n'
  | eraseWff {n n' : RBNode} {k : Nat} : WellFormed n → n' = erase k n → WellFormed n'

end RBNode

open RBNode

def RBMap : Type :=
  {t : RBNode // t.WellFormed }

@[inline] def RBMap.empty : RBMap :=
  ⟨leaf, WellFormed.leafWff⟩

namespace RBMap

@[inline] def insert : RBMap → Nat → Bool → RBMap
  | ⟨t, w⟩, k, v => ⟨t.insert k v, WellFormed.insertWff w rfl⟩

@[inline] def fold (f : σ → Nat → Bool → σ) : (init : σ) → RBMap → σ
  | b, ⟨t, _⟩ => t.fold f b

end RBMap

abbrev Tree := RBMap

def mkMapAux : Nat → Tree → Tree
  | 0,   m => m
  | n+1, m => mkMapAux n (RBMap.insert m n (n % 10 = 0))

def mkMap (n : Nat) :=
  mkMapAux n RBMap.empty

end RBMapMono

def rbmap_mono (n: Nat): Nat :=
  let m := RBMapMono.mkMap n
  let v := m.fold (fun r _ v => if v then r + 1 else r) 0
  v
