/-
This is rbmap_std_mono but directly manipulating RBNode without the invariant.
Should correspond closely to what the "old" rbmap is doing.
-/

namespace RBMapRaw

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

end RBNode

open RBNode

abbrev Tree := RBNode

def mkMapAux : Nat → Tree → Tree
  | 0,   m => m
  | n+1, m => mkMapAux n (m.insert n (n % 10 = 0))

def mkMap (n : Nat) :=
  mkMapAux n .leaf

end RBMapRaw

def rbmap_raw (n: Nat): Nat :=
  let m := RBMapRaw.mkMap n
  let v := m.fold (fun r _ v => if v then r + 1 else r) 0
  v
