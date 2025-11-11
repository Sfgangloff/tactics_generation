import Batteries

open Std

def countBinarySeq (n : Nat) : Float := Id.run do
  let mut nCr : Float := 1.0
  let mut res : Float := 1.0
  for r in [1 : n + 1] do
    nCr := (nCr * Float.ofNat (n + 1 - r)) / Float.ofNat r
    res := res + nCr * nCr
  return res

#guard countBinarySeq 1 == 2.0
#guard countBinarySeq 2 == 6.0
#guard countBinarySeq 3 == 20.0
