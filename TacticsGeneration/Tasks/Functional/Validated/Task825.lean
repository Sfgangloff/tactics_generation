import Batteries

open Std

def accessElements (nums : List Nat) (listIndex : List Nat) : List Nat :=
  
  listIndex.map (fun i => nums.getD i 0)

#guard accessElements [2,3,8,4,7,9] [0,3,5] = [2, 4, 9]
#guard accessElements [1, 2, 3, 4, 5] [1,2] = [2,3]
#guard accessElements [1,0,2,3] [0,1] = [1,0]
