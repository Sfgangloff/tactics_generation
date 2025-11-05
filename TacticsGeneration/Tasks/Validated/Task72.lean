import Batteries

open Std

def difSquare (n : Int) : Bool :=
  if n % 4 != 2 then true else false

#guard difSquare 5 == true
#guard difSquare 10 == false
#guard difSquare 15 == true
