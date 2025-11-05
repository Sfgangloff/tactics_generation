import Batteries

open Std

def findLists (Input : List (List Nat)) : Nat :=
  Input.length

#guard findLists [[1, 2, 3, 4], [5, 6, 7, 8]] = 2
#guard findLists [[1, 2], [3, 4], [5, 6]] = 3
#guard findLists [[9, 8, 7, 6, 5, 4, 3, 2, 1]] = 1
