import Batteries

open Std

def surfaceareaSphere (r : Nat) : Float :=
  let rr := Float.ofNat r
  (4.0 : Float) * (3.141592653589793 : Float) * rr * rr

#guard surfaceareaSphere 10 == (1256.6370614359173 : Float)
#guard surfaceareaSphere 15 == (2827.4333882308138 : Float)
#guard surfaceareaSphere 20 == (5026.548245743669 : Float)
