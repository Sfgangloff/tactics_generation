import Batteries

open Std

def emptyDit (list1 : List (List Nat)) : Bool :=
  list1.foldl (fun acc d => acc && d.isEmpty) true

#guard emptyDit [[], [], []] == true
#guard emptyDit [[1, 2], [], []] == false
#guard emptyDit ([] : List (List Nat)) == true
