import Batteries

open Std

def factorial (start end_ : Nat) : Nat := Id.run do
  let mut res := 1
  for i in [start : end_ + 1] do
    res := res * i
  return res

def sumOfSquare (n : Nat) : Nat :=
  (factorial (n + 1) (2 * n)) / (factorial 1 n)

#guard sumOfSquare 4 = 70
#guard sumOfSquare 5 = 252
#guard sumOfSquare 2 = 6
