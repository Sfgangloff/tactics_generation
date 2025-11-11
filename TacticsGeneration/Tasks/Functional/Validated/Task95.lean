import Batteries

open Std

def findMinLength (lst : List (List Nat)) : Nat :=
  lst.foldl (fun acc x => Nat.min acc x.length) (lst.head!.length)

#guard findMinLength [[1], [1, 2]] = 1
#guard findMinLength [[1, 2], [1, 2, 3], [1, 2, 3, 4]] = 2
#guard findMinLength [[3, 3, 3], [4, 4, 4, 4]] = 3
