import Batteries

open Std

def power_base_sum (base power : Nat) : Nat :=
  let s := toString (Nat.pow base power)
  s.data.foldl (fun acc c => acc + (c.toNat - '0'.toNat)) 0

#guard power_base_sum 2 100 = 115
#guard power_base_sum 8 10 = 37
#guard power_base_sum 8 15 = 62
