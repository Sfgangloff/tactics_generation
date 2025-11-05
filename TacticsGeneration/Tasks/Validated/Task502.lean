import Batteries

open Std

def find (n m : Nat) : Nat :=
  let r := n % m
  r

#guard find 3 3 = 0
#guard find 10 3 = 1
#guard find 16 5 = 1
