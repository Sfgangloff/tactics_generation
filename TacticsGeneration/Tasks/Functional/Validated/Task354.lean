import Batteries

open Std

def tnAp (a n d : Nat) : Nat :=
  a + (n - 1) * d

#guard tnAp 1 5 2 = 9
#guard tnAp 2 6 4 = 22
#guard tnAp 1 4 5 = 16
