import Batteries

open Std

def sectorArea (r a : Nat) : Option Float :=
  let pi : Float := 22.0 / 7.0
  if a >= 360 then
    none
  else
    let sectorarea := (pi * Float.ofNat (r * r)) * (Float.ofNat a / 360.0)
    some sectorarea

#guard sectorArea 4 45 == some 6.285714285714286
#guard sectorArea 9 45 == some 31.82142857142857
#guard sectorArea 9 360 == none
