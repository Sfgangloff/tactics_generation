import Batteries
open Std

def pow2Float (k : Nat) : Float :=
  Float.ofNat (Nat.pow 2 k)

private def geometricSumNat : Nat -> Float
| 0 => 1.0 / pow2Float 0
| Nat.succ k => (1.0 / pow2Float (Nat.succ k)) + geometricSumNat k

def geometricSum (n : Int) : Float :=
  if n < 0 then
    0.0
  else
    geometricSumNat (Int.toNat n)

#guard geometricSum 7 == 1.9921875
#guard geometricSum 4 == 1.9375
#guard geometricSum 8 == 1.99609375
