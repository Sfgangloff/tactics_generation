import Batteries

open Std

partial def dealnnoyNum (n m : Nat) : Nat :=
  if m == 0 || n == 0 then
    1
  else
    dealnnoyNum (m - 1) n
    + dealnnoyNum (m - 1) (n - 1)
    + dealnnoyNum m (n - 1)

#guard dealnnoyNum 3 4 = 129
#guard dealnnoyNum 3 3 = 63
#guard dealnnoyNum 4 5 = 681
