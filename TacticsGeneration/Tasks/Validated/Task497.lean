import Batteries
open Std

def surfacearea_cone (r h : Nat) : Float :=
  let rf := (Float.ofNat r)
  let hf := (Float.ofNat h)
  let l := Float.sqrt (rf * rf + hf * hf)
  3.141592653589793 * rf * (rf + l)

#guard surfacearea_cone 5 12 == 282.7433388230814
#guard surfacearea_cone 10 15 == 880.5179353159282
#guard surfacearea_cone 19 17 == 2655.923961165254
