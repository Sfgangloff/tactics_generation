import Batteries

open Std

def unionElements (t1 t2 : List Nat) : HashSet Nat :=
  HashSet.ofList (t1 ++ t2)

#guard unionElements [3, 4, 5, 6] [5, 7, 4, 10] == HashSet.ofList [3, 4, 5, 6, 7, 10]
#guard unionElements [1, 2, 3, 4] [3, 4, 5, 6] == HashSet.ofList [1, 2, 3, 4, 5, 6]
#guard unionElements [11, 12, 13, 14] [13, 15, 16, 17] == HashSet.ofList [11, 12, 13, 14, 15, 16, 17]
