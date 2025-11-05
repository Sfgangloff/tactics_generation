import Batteries

open Std

def isDiff (n : Int) : Bool :=
  n % 11 == 0

#guard isDiff 12345 == false
#guard isDiff 1212112 == true
#guard isDiff 1212 == false
