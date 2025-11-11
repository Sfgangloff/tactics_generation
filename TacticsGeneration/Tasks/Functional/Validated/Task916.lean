import Batteries

open Std

def findTripletArray (A : List Nat) (arr_size : Nat) (sum : Nat) : Option (Nat × Nat × Nat) := Id.run do
  
  for i in [0 : arr_size - 2] do
    for j in [i + 1 : arr_size - 1] do
      for k in [j + 1 : arr_size] do
        if A.getD i 0 + A.getD j 0 + A.getD k 0 == sum then
          return some (A.getD i 0, A.getD j 0, A.getD k 0)
  return none

#guard findTripletArray [1, 4, 45, 6, 10, 8] 6 22 == some (4, 10, 8)
#guard findTripletArray [12, 3, 5, 2, 6, 9] 6 24 == some (12, 3, 9)
#guard findTripletArray [1, 2, 3, 4, 5] 5 9 == some (1, 3, 5)
