import Batteries

open Std

def sqrtRoot (num : Nat) : Nat :=
  
  Nat.sqrt num

#guard sqrtRoot 4 = 2
#guard sqrtRoot 16 = 4
#guard sqrtRoot 400 = 20
