import Batteries

open Std

def listTuple (listx : List Nat) : List Nat :=
  listx

#guard listTuple [5, 10, 7, 4, 15, 3] == [5, 10, 7, 4, 15, 3]
#guard listTuple [2, 4, 5, 6, 2, 3, 4, 4, 7] == [2, 4, 5, 6, 2, 3, 4, 4, 7]
#guard listTuple [58, 44, 56] == [58, 44, 56]
