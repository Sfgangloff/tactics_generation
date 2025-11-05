import Batteries

open Std

def rombusPerimeter (a : Nat) : Nat :=
  let perimeter := 4 * a
  perimeter

#guard rombusPerimeter 10 == 40
#guard rombusPerimeter 5 == 20
#guard rombusPerimeter 4 == 16
