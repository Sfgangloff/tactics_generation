import Batteries

open Std

def surfacearea_cube (l : Nat) : Nat :=
  let surfacearea := 6 * l * l
  surfacearea

#guard surfacearea_cube 5 = 150
#guard surfacearea_cube 3 = 54
#guard surfacearea_cube 10 = 600
