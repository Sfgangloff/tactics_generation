import Batteries

open Std

def circleCircumference (r : Nat) : Float :=
  let perimeter := 2.0 * 3.1415 * (Nat.toFloat r)
  perimeter

#guard circleCircumference 10 == 62.830000000000005
#guard circleCircumference 5 == 31.415000000000003
#guard circleCircumference 4 == 25.132
