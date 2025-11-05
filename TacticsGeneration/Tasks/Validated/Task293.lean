import Batteries

open Std

def otherside_rightangle (w h : Float) : Float :=
  Float.sqrt ((w * w) + (h * h))

#guard otherside_rightangle 7.0 8.0 == 10.63014581273465
#guard otherside_rightangle 3.0 4.0 == 5.0
#guard otherside_rightangle 7.0 15.0 == 16.55294535724685
