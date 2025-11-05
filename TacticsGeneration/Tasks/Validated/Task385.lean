import Batteries

open Std

def getPerrin (n : Nat) : Nat :=
  match n with
  | 0 => 3
  | 1 => 0
  | 2 => 2
  | n+3 => getPerrin (n+1) + getPerrin n

#guard getPerrin 9 = 12
#guard getPerrin 4 = 2
#guard getPerrin 6 = 5
