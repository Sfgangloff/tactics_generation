import Batteries

open Std

def areaPentagon (a : Nat) : Float :=
  let af := Float.ofNat a
  let inner := 5.0 + 2.0 * Float.sqrt 5.0
  let v := Float.sqrt (5.0 * inner)
  (v * (af * af)) / 4.0

#guard areaPentagon 5 == 43.01193501472417
#guard areaPentagon 10 == 172.0477400588967
#guard areaPentagon 15 == 387.10741513251753
