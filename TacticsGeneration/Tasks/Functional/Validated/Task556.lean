import Batteries

open Std

def find_Odd_Pair (A : List Nat) (N : Nat) : Nat := Id.run do
  let mut oddPair := 0
  for i in [0:N] do
    for j in [i+1:N] do
      let ai := A.getD i 0
      let aj := A.getD j 0
      if ((ai ^^^ aj) % 2) != 0 then
        oddPair := oddPair + 1
  return oddPair

#guard find_Odd_Pair [5,4,7,2,1] 5 = 6
#guard find_Odd_Pair [7,2,8,1,0,5,11] 7 = 12
#guard find_Odd_Pair [1,2,3] 3 = 2
