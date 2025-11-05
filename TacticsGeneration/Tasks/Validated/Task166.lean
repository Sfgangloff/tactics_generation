import Batteries

open Std

def find_even_Pair (A : List Nat) (N : Nat) : Nat := Id.run do
  let mut evenPair := 0
  for i in [0:N] do
    for j in [i+1:N] do
      let ai := A.getD i 0
      let aj := A.getD j 0
      if ((ai ^^^ aj) % 2 == 0) then
        evenPair := evenPair + 1
  return evenPair

#guard find_even_Pair [5,4,7,2,1] 5 = 4
#guard find_even_Pair [7,2,8,1,0,5,11] 7 = 9
#guard find_even_Pair [1,2,3] 3 = 1
