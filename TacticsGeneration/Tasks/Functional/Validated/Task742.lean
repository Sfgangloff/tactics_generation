import Batteries

open Std

def areaTetrahedron (side : Float) : Float :=
  Float.sqrt 3.0 * (side * side)

#guard areaTetrahedron 3.0 == 15.588457268119894
#guard areaTetrahedron 20.0 == 692.8203230275509
#guard areaTetrahedron 10.0 == 173.20508075688772
