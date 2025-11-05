import Batteries

open Std

def lateralsurface_cone (r h : Nat) : Float :=
  let rf := Float.ofNat r
  let hf := Float.ofNat h
  let l := Float.sqrt (rf * rf + hf * hf)
  ((3.141592653589793 : Float) * rf * l)

#guard lateralsurface_cone 5 12 == (204.20352248333654 : Float)
#guard lateralsurface_cone 10 15 == (566.3586699569488 : Float)
#guard lateralsurface_cone 19 17 == (1521.8090132193388 : Float)
