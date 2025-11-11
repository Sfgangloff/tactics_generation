import Batteries

open Std

def parabolaFocus (a b c : Float) : Float × Float :=
  let focus := (-b / (2 * a), ((4 * a * c) - (b * b) + 1) / (4 * a))
  focus

#guard parabolaFocus 5 3 2 == (-0.3, 1.6)
#guard parabolaFocus 9 8 4 == (-0.4444444444444444, 2.25)
#guard parabolaFocus 2 4 6 == (-1.0, 4.125)
