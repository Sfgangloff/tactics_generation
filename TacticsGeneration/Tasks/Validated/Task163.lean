import Batteries

open Std

def areaPolygon (s l : Float) : Float :=
  let piF : Float := 3.141592653589793
  let area := s * (l * l) / (4.0 * Float.tan (piF / s))
  area

#guard areaPolygon 4.0 20.0 == 400.00000000000006
#guard areaPolygon 10.0 15.0 == 1731.1969896610804
#guard areaPolygon 9.0 7.0 == 302.90938549487214
