import Batteries

open Std

def volumeCone (r h : Float) : Float :=
  let volume := (1.0 / 3.0) * 3.141592653589793 * r * r * h
  volume

#guard volumeCone 5.0 12.0 == 314.15926535897927
#guard volumeCone 10.0 15.0 == 1570.7963267948965
#guard volumeCone 19.0 17.0 == 6426.651371693521
