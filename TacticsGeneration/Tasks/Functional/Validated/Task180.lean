import Batteries
open Std

def distanceLatLong (slat slon elat elon : Float) : Float :=
  let dist := 6371.01 * Float.acos (Float.sin slat * Float.sin elat + Float.cos slat * Float.cos elat * Float.cos (slon - elon))
  dist

def approxEq (a b tol : Float) : Bool :=
  let d := if a >= b then a - b else b - a
  decide (d ≤ tol)

#guard approxEq (distanceLatLong 23.5 67.5 25.5 69.5) 12179.372041317429 1e-9
#guard approxEq (distanceLatLong 10.5 20.5 30.5 40.5) 6069.397933300514 1e-9
#guard approxEq (distanceLatLong 10.0 20.0 30.0 40.0) 6783.751974994595 1e-9
