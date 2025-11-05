import Batteries

open Std

def sumNum (numbers : List Int) : Float := Id.run do
  let mut total : Int := 0
  for x in numbers do
    total := total + x
  let n := numbers.length
  return (Float.ofInt total) / (Float.ofNat n)

#guard sumNum [8, 2, 3, 0, 7] == 4.0
#guard sumNum [-10, -20, -30] == -20.0
#guard sumNum [19, 15, 18] == 17.333333333333332
