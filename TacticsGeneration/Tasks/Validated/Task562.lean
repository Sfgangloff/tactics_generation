import Batteries

open Std

def Find_Max_Length (lst : List (List Nat)) : Nat :=
  lst.foldl (fun acc x => Nat.max acc x.length) 0

#guard Find_Max_Length [[1], [1,4], [5,6,7,8]] = 4
#guard Find_Max_Length [[0,1], [2,2], [3,2,1]] = 3
#guard Find_Max_Length [[7], [22,23], [13,14,15], [10,20,30,40,50]] = 5
