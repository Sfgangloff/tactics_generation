import Batteries

open Std

def rectangleArea (l b : Nat) : Nat :=
  let area := l * b
  area

#guard rectangleArea 10 20 == 200
#guard rectangleArea 10 5 == 50
#guard rectangleArea 4 2 == 8
