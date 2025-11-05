import Batteries
open Std

def findIndex (n : Nat) : Nat :=
  let t := 2 * Nat.pow 10 (n - 1)
  let s := Nat.sqrt t
  let s2 := s * s
  let next2 := (s + 1) * (s + 1)
  let d1 := t - s2
  let d2 := next2 - t
  if d1 < d2 then s else s + 1

#guard findIndex 2 = 4
#guard findIndex 3 = 14
#guard findIndex 4 = 45
