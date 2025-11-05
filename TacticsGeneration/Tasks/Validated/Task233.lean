import Batteries

open Std

def lateralsuface_cylinder (r h : Nat) : Float :=
  2.0 * 3.1415 * (Float.ofNat r) * (Float.ofNat h)

#guard lateralsuface_cylinder 10 5 == (314.15000000000003 : Float)
#guard lateralsuface_cylinder 4 5 == (125.66000000000001 : Float)
#guard lateralsuface_cylinder 4 10 == (251.32000000000002 : Float)
