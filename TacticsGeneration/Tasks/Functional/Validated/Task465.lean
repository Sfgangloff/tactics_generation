import Batteries

open Std

def dropEmpty (dict1 : List (String × Option String)) : List (String × String) :=
  dict1.filterMap (fun (k, v) => match v with | some s => some (k, s) | none => none)

#guard dropEmpty [("c1", some "Red"), ("c2", some "Green"), ("c3", none)] == [("c1", "Red"), ("c2", "Green")]
#guard dropEmpty [("c1", some "Red"), ("c2", none), ("c3", none)] == [("c1", "Red")]
#guard dropEmpty [("c1", none), ("c2", some "Green"), ("c3", none)] == [("c2", "Green")]
