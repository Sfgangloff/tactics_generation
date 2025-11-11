import Batteries

open Std

def intersectionArray (arrayNums1 arrayNums2 : List Nat) : List Nat :=
  arrayNums2.filter (fun x => arrayNums1.contains x)

#guard intersectionArray [1, 2, 3, 5, 7, 8, 9, 10] [1, 2, 4, 8, 9] == [1, 2, 8, 9]
#guard intersectionArray [1, 2, 3, 5, 7, 8, 9, 10] [3, 5, 7, 9] == [3, 5, 7, 9]
#guard intersectionArray [1, 2, 3, 5, 7, 8, 9, 10] [10, 20, 30, 40] == [10]
