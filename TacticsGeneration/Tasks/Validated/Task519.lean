import Batteries

open Std

def volumeTetrahedron (num : Nat) : Float :=
  let n := num.toFloat
  let n3 := n * n * n
  let denom := 6.0 * Float.sqrt 2.0
  let volume := n3 / denom
  (Float.round (volume * 100.0)) / 100.0

#guard volumeTetrahedron 10 == 117.85
#guard volumeTetrahedron 15 == 397.75
#guard volumeTetrahedron 20 == 942.81
