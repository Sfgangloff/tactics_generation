import Batteries

open Std

def addLists (testList : List Nat) (testTup : List Nat) : List Nat :=
  testTup ++ testList

#guard addLists [5, 6, 7] [9, 10] = [9, 10, 5, 6, 7]
#guard addLists [6, 7, 8] [10, 11] = [10, 11, 6, 7, 8]
#guard addLists [7, 8, 9] [11, 12] = [11, 12, 7, 8, 9]
