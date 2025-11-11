import Batteries

open Std

def find_Sum (arr : List Nat) (n : Nat) : Nat := Id.run do
  let mut seen : HashSet Nat := {}
  let mut s : Nat := 0
  for x in arr do
    if !(seen.contains x) then
      s := s + x
      seen := seen.insert x
  return s

#guard find_Sum [1,2,3,1,1,4,5,6] 8 = 21
#guard find_Sum [1,10,9,4,2,10,10,45,4] 9 = 71
#guard find_Sum [12,10,9,45,2,10,10,45,10] 9 = 78
