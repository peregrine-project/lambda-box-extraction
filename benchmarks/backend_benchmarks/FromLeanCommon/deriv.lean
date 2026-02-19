/- Benchmark for new code generator -/
/-
Adaptations to make it run with erasure to λbox:
- removed IO wrapper and printing
-/

namespace Deriv

inductive Expr
| Val : Int → Expr
| Var : Nat → Expr
| Add : Expr → Expr → Expr
| Mul : Expr → Expr → Expr
| Pow : Expr → Expr → Expr
| Ln  : Expr → Expr

namespace Expr

partial def pown : Int → Int → Int
| _, 0 => 1
| a, 1 => a
| a, n =>
  let b := pown a (n / 2);
  b * b * (if n % 2 = 0 then 1 else a)

partial def add : Expr → Expr → Expr
| Val n,     Val m           => Val (n + m)
| Val 0,     f               => f
| f,         Val 0           => f
| f,         Val n           => add (Val n) f
| Val n,     Add (Val m) f   => add (Val (n+m)) f
| f,         Add (Val n) g   => add (Val n) (add f g)
| Add f g,   h               => add f (add g h)
| f,         g               => Add f g

partial def mul : Expr → Expr → Expr
| Val n,     Val m           => Val (n*m)
| Val 0,     _               => Val 0
| _,         Val 0           => Val 0
| Val 1,     f               => f
| f,         Val 1           => f
| f,         Val n           => mul (Val n) f
| Val n,     Mul (Val m) f   => mul (Val (n*m)) f
| f,         Mul (Val n) g   => mul (Val n) (mul f g)
| Mul f g,   h               => mul f (mul g h)
| f,         g               => Mul f g

def pow : Expr → Expr → Expr
| Val m,   Val n   => Val (pown m n)
| _,       Val 0   => Val 1
| f,       Val 1   => f
| Val 0,   _       => Val 0
| f,       g       => Pow f g

def ln : Expr → Expr
| Val 1   => Val 0
| f       => Ln f

def d (x : Nat) : Expr → Expr
| Val _     => Val 0
| Var y     => if x = y then Val 1 else Val 0
| Add f g   => add (d x f) (d x g)
| Mul f g   => add (mul f (d x g)) (mul g (d x f))
| Pow f g   => mul (pow f g) (add (mul (mul g (d x f)) (pow f (Val (-1)))) (mul (ln f) (d x g)))
| Ln f      => mul (d x f) (pow f (Val (-1)))

def count : Expr → Nat
| Val _   => 1
| Var _   => 1
| Add f g   => count f + count g
| Mul f g   => count f + count g
| Pow f g   => count f + count g
| Ln f      => count f

def nestAux (s : Nat) (f : Nat → Expr → Expr) : Nat → Expr → Expr
| 0,       e => e
| m@(n+1), e => f (s - m) e |> nestAux s f n

def nest (f : Nat → Expr → Expr) (n : Nat) (e : Expr) : Expr :=
nestAux n f n e

def deriv (_ : Nat) (e : Expr) : Expr :=
  d 0 e

end Expr
end Deriv

open Deriv Expr

def deriv (n: Nat): Nat :=
  let e := pow (Var 0) (Var 0);
  nest Deriv.Expr.deriv n e |> count
