import Batteries

open Std

def volumeCylinder (r h : Nat) : Float :=
  3.1415 * (Float.ofNat r) * (Float.ofNat r) * (Float.ofNat h)

#guard volumeCylinder 10 5 == 1570.7500000000002
#guard volumeCylinder 4 5 == 251.32000000000002
#guard volumeCylinder 4 10 == 502.64000000000004
