import Batteries

open Std

def is_polite (n : Nat) : Nat :=
  let m := n + 1
  let t := m + Nat.log2 m
  m + Nat.log2 t

#guard is_polite 7 = 11
#guard is_polite 4 = 7
#guard is_polite 9 = 13
