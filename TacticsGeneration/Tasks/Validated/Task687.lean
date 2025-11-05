import Batteries

open Std

partial def recurGcd (a b : Nat) : Nat :=
  let low := Nat.min a b
  let high := Nat.max a b
  if low == 0 then
    high
  else if low == 1 then
    1
  else
    recurGcd low (high % low)

#guard recurGcd 12 14 == 2
#guard recurGcd 13 17 == 1
#guard recurGcd 9 3 == 3
