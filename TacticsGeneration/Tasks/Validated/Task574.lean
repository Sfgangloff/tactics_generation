import Batteries

open Std

def surfacearea_cylinder (r h : Nat) : Float :=
  let rf := Float.ofNat r
  let hf := Float.ofNat h
  let surfacearea := ((2.0 * 3.1415 * rf * rf) + (2.0 * 3.1415 * rf * hf))
  surfacearea

#guard surfacearea_cylinder 10 5 == (942.45 : Float)
#guard surfacearea_cylinder 4 5 == (226.18800000000002 : Float)
#guard surfacearea_cylinder 4 10 == (351.848 : Float)
