import Batteries

open Std

def lastDigit (n : Nat) : Nat :=
  n % 10

#guard lastDigit 123 = 3
#guard lastDigit 25 = 5
#guard lastDigit 30 = 0
