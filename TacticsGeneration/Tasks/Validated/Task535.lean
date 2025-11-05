import Batteries

open Std

def topbottom_surfacearea (r : Float) : Float :=
  let toporbottomarea := (3.1415 : Float) * r * r
  toporbottomarea

#guard topbottom_surfacearea 10.0 == 314.15000000000003
#guard topbottom_surfacearea 5.0 == 78.53750000000001
#guard topbottom_surfacearea 4.0 == 50.264
