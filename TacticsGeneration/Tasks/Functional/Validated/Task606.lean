import Batteries

open Std

def radianDegree (degree : Nat) : Float :=
  let piConst : Float := 3.141592653589793
  let radian := (Float.ofNat degree) * (piConst / 180.0)
  radian

#guard radianDegree 90 == 1.5707963267948966
#guard radianDegree 60 == 1.0471975511965976
#guard radianDegree 120 == 2.0943951023931953
