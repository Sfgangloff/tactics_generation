import Batteries

open Std

def tnGp (a r n : Nat) : Nat :=
  a * r^(n - 1)

#guard tnGp 1 2 5 == 16
#guard tnGp 1 4 5 == 256
#guard tnGp 2 3 6 == 486
