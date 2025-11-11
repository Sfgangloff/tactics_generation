import Batteries

open Std

def medianNumbers (a b c : Nat) : Float :=
  let median :=
    if a > b then
      if a < c then a
      else if b > c then b
      else c
    else
      if a > c then a
      else if b < c then b
      else c
  Float.ofNat median

#guard medianNumbers 25 55 65 == 55.0
#guard medianNumbers 20 10 30 == 20.0
#guard medianNumbers 15 45 75 == 45.0
