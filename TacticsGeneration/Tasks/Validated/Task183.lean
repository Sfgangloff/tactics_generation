import Batteries

open Std

def countPairs (arr : List Nat) (n : Nat) (k : Nat) : Nat := Id.run do
  
  let a := arr.toArray
  let mut count := 0
  for i in [0 : n] do
    for j in [i+1 : n] do
      let xi := a.getD i 0
      let xj := a.getD j 0
      if (xi - xj == k) || (xj - xi == k) then
        count := count + 1
  return count

#guard countPairs [1, 5, 3, 4, 2] 5 3 = 2
#guard countPairs [8, 12, 16, 4, 0, 20] 6 4 = 5
#guard countPairs [2, 4, 1, 3, 4] 5 2 = 3
