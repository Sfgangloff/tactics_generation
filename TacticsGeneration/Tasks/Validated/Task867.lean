import Batteries

open Std

def min_Num (arr : List Nat) (n : Nat) : Nat := Id.run do
  let a := arr.toArray
  let mut odd := 0
  for i in [: n] do
    if a[i]! % 2 == 1 then
      odd := odd + 1
  if odd % 2 == 1 then
    return 1
  return 2

#guard min_Num [1,2,3,4,5,6,7,8,9] 9 = 1
#guard min_Num [1,2,3,4,5,6,7,8] 8 = 2
#guard min_Num [1,2,3] 3 = 2
