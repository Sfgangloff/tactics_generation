import Batteries

open Std

def getNumber (n k : Nat) : Nat := Id.run do
  let mut arr := Array.replicate n 0
  let mut i := 0
  let countOdds := (n + 1) / 2
  for j in [: countOdds] do
    arr := arr.set! i (2 * j + 1)
    i := i + 1
  let countEvens := n / 2
  for j in [: countEvens] do
    arr := arr.set! i (2 * (j + 1))
    i := i + 1
  return arr[k - 1]!

#guard getNumber 8 5 = 2
#guard getNumber 7 2 = 3
#guard getNumber 5 2 = 3
