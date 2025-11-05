import Batteries

open Std

def containsNat (l : List Nat) (x : Nat) : Bool :=
  l.foldl (fun acc y => acc || y == x) false

def checkTuples (testTuple : List Nat) (K : List Nat) : Bool :=
  testTuple.foldl (fun acc ele => acc && containsNat K ele) true

#guard checkTuples [3, 5, 6, 5, 3, 6] [3, 6, 5] == true
#guard checkTuples [4, 5, 6, 4, 6, 5] [4, 5, 6] == true
#guard checkTuples [9, 8, 7, 6, 8, 9] [9, 8, 1] == false
