import Batteries

open Std

def sumDifference (n : Nat) : Nat := Id.run do
  let mut sumofsquares := 0
  let mut squareofsum := 0
  for num in [1 : n+1] do
    sumofsquares := sumofsquares + num * num
    squareofsum := squareofsum + num
  squareofsum := squareofsum ^ 2
  return squareofsum - sumofsquares

#guard sumDifference 12 = 5434
#guard sumDifference 20 = 41230
#guard sumDifference 54 = 2151270
