import Batteries

open Std

def lastTwoDigits (N : Nat) : Option Nat :=
  if N >= 10 then
    none
  else
    let fac := Id.run do
      let mut fac := 1
      for i in [1 : N + 1] do
        fac := (fac * i) % 100
      return fac
    some fac

#guard lastTwoDigits 7 = some 40
#guard lastTwoDigits 5 = some 20
#guard lastTwoDigits 2 = some 2
