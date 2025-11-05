import Batteries

open Std

def arcLength (d a : Nat) : Option Float :=
  let pi : Float := 22.0 / 7.0
  if a >= 360 then
    none
  else
    let arclength := (pi * Float.ofNat d) * (Float.ofNat a / 360.0)
    some arclength

#guard arcLength 9 45 == some 3.5357142857142856
#guard arcLength 9 480 == none
#guard arcLength 5 270 == some 11.785714285714285
