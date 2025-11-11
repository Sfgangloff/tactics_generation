import Batteries

open Std

def parabolaVertex (a b c : Float) : Float × Float :=
  let vertex := ((-b / (2 * a)), (((4 * a * c) - (b * b)) / (4 * a)))
  vertex

#guard parabolaVertex 5 3 2 == (-0.3, 1.55)
#guard parabolaVertex 9 8 4 == (-0.4444444444444444, 2.2222222222222223)
#guard parabolaVertex 2 4 6 == (-1.0, 4.0)
