import Batteries

open Std

def INT_BITS : Nat := 32

def left_Rotate (n d : Nat) : Nat :=
  Nat.lor (Nat.shiftLeft n d) (Nat.shiftRight n (INT_BITS - d))

#guard left_Rotate 16 2 = 64
#guard left_Rotate 10 2 = 40
#guard left_Rotate 99 3 = 792
