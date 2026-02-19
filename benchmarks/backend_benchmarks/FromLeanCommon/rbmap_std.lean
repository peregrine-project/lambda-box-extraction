-- import Lean.Data.RBMap
/-
Importing from Lean.Data.RBMap imports the entirety of Lean,
which leads to a runtime (!) overhead of about 50ms.
https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/.60import.20Lean.60.20influencing.20executable.20startup.20time
Instead, inlined the necessary bits.
-/

namespace RBMapStd
universe u v

inductive RBColor where
  | red | black

inductive RBNode (α : Type u) (β : α → Type v) where
  | leaf                                                                                        : RBNode α β
  | node  (color : RBColor) (lchild : RBNode α β) (key : α) (val : β key) (rchild : RBNode α β) : RBNode α β

namespace RBNode
variable {α : Type u} {β : α → Type v} {σ : Type w}

open RBColor Nat

-- @[specialize] def fold (f : σ → (k : α) → β k → σ) : (init : σ) → RBNode α β → σ
def fold (f : σ → (k : α) → β k → σ) : (init : σ) → RBNode α β → σ
  | b, leaf           => b
  | b, node _ l k v r => fold f (f (fold f b l) k v) r

-- the first half of Okasaki's `balance`, concerning red-red sequences in the left child
@[inline] def balance1 : RBNode α β → (a : α) → β a → RBNode α β → RBNode α β
  | node red (node red a kx vx b) ky vy c, kz, vz, d
  | node red a kx vx (node red b ky vy c), kz, vz, d => node red (node black a kx vx b) ky vy (node black c kz vz d)
  | a,                                     kx, vx, b => node black a kx vx b

-- the second half, concerning red-red sequences in the right child
@[inline] def balance2 : RBNode α β → (a : α) → β a → RBNode α β → RBNode α β
  | a, kx, vx, node red (node red b ky vy c) kz vz d
  | a, kx, vx, node red b ky vy (node red c kz vz d) => node red (node black a kx vx b) ky vy (node black c kz vz d)
  | a, kx, vx, b                                     => node black a kx vx b

def isRed : RBNode α β → Bool
  | node red .. => true
  | _           => false

def isBlack : RBNode α β → Bool
  | node black .. => true
  | _             => false

section Insert

variable (cmp : α → α → Ordering)

@[specialize] def ins : RBNode α β → (k : α) → β k → RBNode α β
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

def setBlack : RBNode α β → RBNode α β
  | node _ l k v r => node black l k v r
  | e              => e

@[specialize] def insert (t : RBNode α β) (k : α) (v : β k) : RBNode α β :=
  if isRed t then setBlack (ins cmp t k v)
  else ins cmp t k v

end Insert

def setRed : RBNode α β → RBNode α β
  | node _ a k v b => node red a k v b
  | e              => e

def balLeft : RBNode α β → (k : α) → β k → RBNode α β → RBNode α β
  | node red a kx vx b,   k, v, r                    => node red (node black a kx vx b) k v r
  | l, k, v, node black a ky vy b                    => balance2 l k v (node red a ky vy b)
  | l, k, v, node red (node black a ky vy b) kz vz c => node red (node black l k v a) ky vy (balance2 b kz vz (setRed c))
  | l, k, v, r                                       => node red l k v r -- unreachable

def balRight (l : RBNode α β) (k : α) (v : β k) (r : RBNode α β) : RBNode α β :=
  match r with
  | (node red b ky vy c) => node red l k v (node black b ky vy c)
  | _ => match l with
    | node black a kx vx b                    => balance1 (node red a kx vx b) k v r
    | node red a kx vx (node black b ky vy c) => node red (balance1 (setRed a) kx vx b) ky vy (node black c k v r)
    | _                                       => node red l k v r -- unreachable

/-- The number of nodes in the tree. -/
@[local simp] def size : RBNode α β → Nat
  | leaf => 0
  | node _ x _ _ y => x.size + y.size + 1

def appendTrees :  RBNode α β → RBNode α β → RBNode α β
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

variable (cmp : α → α → Ordering)

@[specialize] def del (x : α) : RBNode α β → RBNode α β
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

@[specialize] def erase (x : α) (t : RBNode α β) : RBNode α β :=
  let t := del cmp x t;
  t.setBlack

end Erase

inductive WellFormed (cmp : α → α → Ordering) : RBNode α β → Prop where
  | leafWff : WellFormed cmp leaf
  | insertWff {n n' : RBNode α β} {k : α} {v : β k} : WellFormed cmp n → n' = insert cmp n k v → WellFormed cmp n'
  | eraseWff {n n' : RBNode α β} {k : α} : WellFormed cmp n → n' = erase cmp k n → WellFormed cmp n'

end RBNode

open RBNode

def RBMap (α : Type u) (β : Type v) (cmp : α → α → Ordering) : Type (max u v) :=
  {t : RBNode α (fun _ => β) // t.WellFormed cmp }

@[inline] def mkRBMap (α : Type u) (β : Type v) (cmp : α → α → Ordering) : RBMap α β cmp :=
  ⟨leaf, WellFormed.leafWff⟩

@[inline] def RBMap.empty {α : Type u} {β : Type v} {cmp : α → α → Ordering} : RBMap α β cmp :=
  mkRBMap ..

namespace RBMap

@[inline] def insert : RBMap α β cmp → α → β → RBMap α β cmp
  | ⟨t, w⟩, k, v => ⟨t.insert cmp k v, WellFormed.insertWff w rfl⟩

@[inline] def fold (f : σ → α → β → σ) : (init : σ) → RBMap α β cmp → σ
  | b, ⟨t, _⟩ => t.fold f b

end RBMap

-- Unsure why this isn't already defined somewhere.
def cmp (n m : Nat) : Ordering :=
  bif n.blt m then .lt
  else bif m.blt n then .gt
  else .eq

abbrev Tree := RBMap Nat Bool cmp

def mkMapAux : Nat → Tree → Tree
  | 0,   m => m
  | n+1, m => mkMapAux n (RBMap.insert m n (n % 10 = 0))

def mkMap (n : Nat) :=
  mkMapAux n RBMap.empty

end RBMapStd

def rbmap_std (n: Nat): Nat :=
  let m := RBMapStd.mkMap n
  let v := m.fold (fun r _ v => if v then r + 1 else r) 0
  v
