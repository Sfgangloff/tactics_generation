import Batteries

open Std

def harmonicSum (n : Nat) : Float :=
  match n with
  | 0 => 1.0
  | 1 => 1.0
  | Nat.succ (Nat.succ k) =>
      1.0 / Float.ofNat (Nat.succ (Nat.succ k)) + harmonicSum (Nat.succ k)

#guard harmonicSum 7 == 2.5928571428571425
#guard harmonicSum 4 == 2.083333333333333
#guard harmonicSum 19 == 3.547739657143682
