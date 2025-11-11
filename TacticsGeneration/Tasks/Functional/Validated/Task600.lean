import Batteries

open Std

def isEven (n : Nat) : Bool :=
  if (n ^^^ 1) == (n + 1) then true else false

#guard isEven 1 == false
#guard isEven 2 == true
#guard isEven 3 == false
