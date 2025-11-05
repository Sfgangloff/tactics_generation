import Batteries

open Std

def allUnique (test_list : List Nat) : Bool :=
  if test_list.length > (HashSet.ofList test_list).size then
    false
  else
    true

#guard allUnique [1, 2, 3] == true
#guard allUnique [1, 2, 1, 2] == false
#guard allUnique [1, 2, 3, 4, 5] == true
