import Batteries

open Std

def checkIdentical (testList1 : List (Nat × Nat)) (testList2 : List (Nat × Nat)) : Bool :=
  testList1 == testList2

#guard checkIdentical [(10, 4), (2, 5)] [(10, 4), (2, 5)] == true
#guard checkIdentical [(1, 2), (3, 7)] [(12, 14), (12, 45)] == false
#guard checkIdentical [(2, 14), (12, 25)] [(2, 14), (12, 25)] == true
