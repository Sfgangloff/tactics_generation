import Batteries

open Std

def find (n m : Nat) : Nat :=
  let q := n / m
  q

#guard find 10 3 = 3
#guard find 4 2 = 2
#guard find 20 5 = 4
