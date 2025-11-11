import Batteries

open Std

def tupleToSet (t : List String) : HashSet String :=
  HashSet.ofList t

#guard tupleToSet ["x", "y", "z"] == HashSet.ofList ["y", "x", "z"]
#guard tupleToSet ["a", "b", "c"] == HashSet.ofList ["c", "a", "b"]
#guard tupleToSet ["z", "d", "e"] == HashSet.ofList ["d", "e", "z"]
