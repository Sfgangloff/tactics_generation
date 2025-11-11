import Batteries

open Std

def isNonagonal (n : Nat) : Nat :=
  (n * (7 * n - 5)) / 2

#guard isNonagonal 10 = 325
#guard isNonagonal 15 = 750
#guard isNonagonal 18 = 1089
