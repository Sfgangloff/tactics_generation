import Batteries

open Std

def volumeSphere (r : Nat) : Float :=
  let pi : Float := 3.141592653589793
  (((4.0 / 3.0) * pi) * (Float.ofNat r)) * (Float.ofNat r) * (Float.ofNat r)

#guard volumeSphere 10 == (4188.790204786391 : Float)
#guard volumeSphere 25 == (65449.84694978735 : Float)
#guard volumeSphere 20 == (33510.32163829113 : Float)
