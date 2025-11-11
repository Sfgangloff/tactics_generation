import Batteries

open Std

def pair_OR_Sum (arr : List Nat) (n : Nat) : Nat := Id.run do
  let a := arr.toArray
  let mut ans := 0
  for i in [0:n] do
    for j in [i+1:n] do
      ans := ans + (a[i]! ^^^ a[j]!)
  return ans

#guard pair_OR_Sum [5,9,7,6] 4 = 47
#guard pair_OR_Sum [7,3,5] 3 = 12
#guard pair_OR_Sum [7,3] 2 = 4
