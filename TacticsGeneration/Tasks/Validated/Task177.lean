import Batteries

open Std

def answer (L R : Nat) : Int × Int :=
  if 2 * L ≤ R then (Int.ofNat L, Int.ofNat (2 * L)) else (-1, -1)

#guard answer 3 8 = ((3, 6) : Int × Int)
#guard answer 2 6 = ((2, 4) : Int × Int)
#guard answer 1 3 = ((1, 2) : Int × Int)
