import Batteries

open Std

def multiplyIntNat (x : Int) (n : Nat) : Int :=
  match n with
  | 0 => 0
  | Nat.succ k => x + multiplyIntNat x k

def multiplyInt (x y : Int) : Int :=
  if y < 0 then
    - multiplyIntNat x (Int.toNat (-y))
  else
    multiplyIntNat x (Int.toNat y)

#guard multiplyInt 10 20 = 200
#guard multiplyInt 5 10 = 50
#guard multiplyInt 4 8 = 32
