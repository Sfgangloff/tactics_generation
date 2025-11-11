import Batteries

open Std

def parallelogramArea (b h : Nat) : Nat :=
  let area := b * h
  area

#guard parallelogramArea 10 20 == 200
#guard parallelogramArea 15 20 == 300
#guard parallelogramArea 8 9 == 72
