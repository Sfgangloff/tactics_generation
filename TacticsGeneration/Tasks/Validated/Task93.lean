import Batteries

open Std

def power (a b : Nat) : Nat :=
  match b with
  | 0 => 1
  | 1 => a
  | Nat.succ (Nat.succ k) =>
      if a == 0 then 0 else a * power a (Nat.succ k)

#guard power 3 4 = 81
#guard power 2 3 = 8
#guard power 5 5 = 3125
