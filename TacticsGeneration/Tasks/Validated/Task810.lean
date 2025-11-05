import Batteries

open Std

def nonnegCount (x : Int) : Nat :=
  if x <= 0 then 0 else Int.toNat x

def countVariable (a b c d : Int) : List String :=
  (List.replicate (nonnegCount a) "p") ++
  (List.replicate (nonnegCount b) "q") ++
  (List.replicate (nonnegCount c) "r") ++
  (List.replicate (nonnegCount d) "s")

#guard countVariable 4 2 0 (-2) == ["p", "p", "p", "p", "q", "q"]
#guard countVariable 0 1 2 3 == ["q", "r", "r", "s", "s", "s"]
#guard countVariable 11 15 12 23 == (List.replicate 11 "p") ++ (List.replicate 15 "q") ++ (List.replicate 12 "r") ++ (List.replicate 23 "s")
