import Batteries

open Std

def sumColumn (list1 : List (List Nat)) (C : Nat) : Nat :=
  list1.foldl (fun acc row => acc + row.getD C 0) 0

#guard sumColumn [[1,2,3,2],[4,5,6,2],[7,8,9,5]] 0 = 12
#guard sumColumn [[1,2,3,2],[4,5,6,2],[7,8,9,5]] 1 = 15
#guard sumColumn [[1,2,3,2],[4,5,6,2],[7,8,9,5]] 3 = 9
