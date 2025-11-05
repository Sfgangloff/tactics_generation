import Batteries
open Std

def multiplyNum (numbers : List Int) : Float :=
  let total := numbers.foldl (· * ·) 1
  let totalFloat := Float.ofInt total
  totalFloat / Float.ofNat numbers.length

#guard multiplyNum [8, 2, 3, -1, 7] == -67.2
#guard multiplyNum [-10, -20, -30] == -2000.0
#guard multiplyNum [19, 15, 18] == 1710.0
