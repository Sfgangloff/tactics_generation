import Batteries

open Std

def count_Squares (m n : Nat) : Nat :=
  let m' := if n < m then n else m
  let n' := if n < m then m else n
  (n' * (n' + 1) * (3 * m' - n' + 1)) / 6

#guard count_Squares 4 3 = 20
#guard count_Squares 1 2 = 2
#guard count_Squares 2 2 = 5
