import Batteries
open Std

def oppositeSigns (x y : Int) : Bool :=
  (x < 0 ∧ y ≥ 0) ∨ (x ≥ 0 ∧ y < 0)

#eval oppositeSigns 1 (-2) == true
#eval oppositeSigns 3 2 == false
#eval oppositeSigns (-10) (-10) == false
