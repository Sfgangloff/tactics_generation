import Batteries

open Std

def dogAge (h : Nat) : Nat :=
  if h ≤ 2 then
    (21 * h) / 2
  else
    21 + (h - 2) * 4

#guard dogAge 12 = 61
#guard dogAge 15 = 73
#guard dogAge 24 = 109
