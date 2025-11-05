import Batteries

open Std

def removeElements (list1 list2 : List Nat) : List Nat :=
  list1.filter (fun x => !(list2.contains x))

#guard removeElements [1,2,3,4,5,6,7,8,9,10] [2,4,6,8] = [1, 3, 5, 7, 9, 10]
#guard removeElements [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [1, 3, 5, 7] = [2, 4, 6, 8, 9, 10]
#guard removeElements [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] [5,7] = [1, 2, 3, 4, 6, 8, 9, 10]
