import Batteries

open Std

def degreeRadian (radian : Nat) : Float :=
  let pi : Float := 3.141592653589793
  (Float.ofNat radian) * (180.0 / pi)

#guard degreeRadian 90 == 5156.620156177409
#guard degreeRadian 60 == 3437.746770784939
#guard degreeRadian 120 == 6875.493541569878
