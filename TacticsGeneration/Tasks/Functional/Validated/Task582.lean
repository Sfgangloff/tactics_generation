import Batteries

open Std

def my_dict (dict1 : HashSet Nat) : Bool :=
  if (! dict1.isEmpty) then false else true

#guard my_dict (HashSet.ofList [10]) == false
#guard my_dict (HashSet.ofList [11]) == false
#guard my_dict (HashSet.empty) == true
