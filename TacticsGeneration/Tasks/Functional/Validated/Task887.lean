import Batteries

open Std

def is_odd (n : Nat) : Bool :=
  (n ^^^ 1) == (n - 1)

#guard is_odd 5 == true
#guard is_odd 6 == false
#guard is_odd 7 == true
