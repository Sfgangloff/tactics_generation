import Batteries

open Std

def checkSmaller (test_tup1 : List Nat) (test_tup2 : List Nat) : Bool :=
  let rec go : List Nat → List Nat → Bool
  | x::xs, y::ys =>
    if h : x > y then
      go xs ys
    else
      false
  | _, _ => true
  go test_tup1 test_tup2

#guard checkSmaller [1, 2, 3] [2, 3, 4] == false
#guard checkSmaller [4, 5, 6] [3, 4, 5] == true
#guard checkSmaller [11, 12, 13] [10, 11, 12] == true
