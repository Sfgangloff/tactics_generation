import Batteries

open Std

def divisor (n : Nat) : Nat :=
  let x := (List.range (n + 1)).drop 1 |>.filter (fun i => n % i == 0) |>.length
  x

#guard divisor 15 == 4
#guard divisor 12 == 6
#guard divisor 9 == 3
