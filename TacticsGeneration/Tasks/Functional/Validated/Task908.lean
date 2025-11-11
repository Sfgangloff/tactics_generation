import Batteries

open Std

def findFixedPoint (arr : List Int) (n : Nat) : Int := Id.run do
  
  let a := arr.toArray
  for i in [: n] do
    let v := a[i]!
    if v == (Int.ofNat i) then
      return Int.ofNat i
  return (-1)

#guard findFixedPoint [-10, -1, 0, 3, 10, 11, 30, 50, 100] 9 = 3
#guard findFixedPoint [1, 2, 3, 4, 5, 6, 7, 8] 8 = (-1)
#guard findFixedPoint [0, 2, 5, 8, 17] 5 = 0
