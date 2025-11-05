import Batteries

open Std

def min_Jumps (a b d : Nat) : Float :=
  let temp := a
  let a' := Nat.min a b
  let b' := Nat.max temp b
  if d >= b' then
    (Float.ofNat (d + b' - 1)) / (Float.ofNat b')
  else if d == 0 then
    0.0
  else if d == a' then
    1.0
  else
    2.0

#guard min_Jumps 3 4 11 == 3.5
#guard min_Jumps 3 4 0 == 0.0
#guard min_Jumps 11 14 11 == 1.0
