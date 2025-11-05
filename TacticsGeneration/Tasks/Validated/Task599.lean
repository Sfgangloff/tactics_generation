import Batteries

open Std

def sumAverage (number : Nat) : Nat × Float := Id.run do
  let mut total : Nat := 0
  for value in [1 : number + 1] do
    total := total + value
  let average : Float := (Float.ofNat total) / (Float.ofNat number)
  return (total, average)

#guard sumAverage 10 == (55, 5.5)
#guard sumAverage 15 == (120, 8.0)
#guard sumAverage 20 == (210, 10.5)
