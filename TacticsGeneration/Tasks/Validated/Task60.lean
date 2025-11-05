import Batteries

open Std

def maxLenSub (arr : List Int) (n : Nat) : Nat := Id.run do
  let a := arr.toArray
  let mut mls : Array Nat := Array.replicate n 1
  for i in [: n] do
    for j in [: i] do
      if Int.natAbs (a[i]! - a[j]!) ≤ 1 && mls[i]! < mls[j]! + 1 then
        mls := mls.set! i (mls[j]! + 1)
  let mut best := 0
  for i in [: n] do
    if best < mls[i]! then
      best := mls[i]!
  return best

#guard maxLenSub ([2, 5, 6, 3, 7, 6, 5, 8] : List Int) 8 == 5
#guard maxLenSub ([-2, -1, 5, -1, 4, 0, 3] : List Int) 7 == 4
#guard maxLenSub ([9, 11, 13, 15, 18] : List Int) 5 == 1
