import Batteries

open Std

def get_key (dict : List (Nat × String)) : List Nat :=
  dict.map (fun p => p.fst)

#guard get_key [(1,"python"), (2,"java")] = [1, 2]
#guard get_key [(10,"red"), (20,"blue"), (30,"black")] = [10, 20, 30]
#guard get_key [(27,"language"), (39,"java"), (44,"little")] = [27, 39, 44]
