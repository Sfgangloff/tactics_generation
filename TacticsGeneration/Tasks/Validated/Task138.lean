import Batteries

open Std

def is_Sum_Of_Powers_Of_Two (n : Nat) : Bool :=
  if n % 2 == 1 then
    false
  else
    true

#guard is_Sum_Of_Powers_Of_Two 10 == true
#guard is_Sum_Of_Powers_Of_Two 7 == false
#guard is_Sum_Of_Powers_Of_Two 14 == true
