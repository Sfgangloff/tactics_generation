import Batteries

open Std

partial def eulerianNum (n m : Nat) : Nat :=
  if (Nat.ble n m) || (n == 0) then
    0
  else if m == 0 then
    1
  else
    let a := (n - m) * eulerianNum (n - 1) (m - 1)
    let b := (m + 1) * eulerianNum (n - 1) m
    a + b

#guard eulerianNum 3 1 = 4
#guard eulerianNum 4 1 = 11
#guard eulerianNum 5 3 = 26
