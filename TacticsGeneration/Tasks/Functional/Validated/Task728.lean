import Batteries

open Std

def sumList (lst1 lst2 : List Nat) : List Nat :=
  List.zipWith (· + ·) lst1 lst2

#guard sumList [10,20,30] [15,25,35] = [25,45,65]
#guard sumList [1,2,3] [5,6,7] = [6,8,10]
#guard sumList [15,20,30] [15,45,75] = [30,65,105]
