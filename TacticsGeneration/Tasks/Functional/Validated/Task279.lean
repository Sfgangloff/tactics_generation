import Batteries

open Std

def isNumDecagonal (n : Nat) : Nat :=
  4 * n * n - 3 * n

#guard isNumDecagonal 3 = 27
#guard isNumDecagonal 7 = 175
#guard isNumDecagonal 10 = 370
