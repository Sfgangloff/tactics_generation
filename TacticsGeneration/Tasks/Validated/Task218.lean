import Batteries

open Std

def minOperations (A B : Nat) : Nat :=
  
  let (a, b) := if A > B then (B, A) else (A, B)
  let g := Nat.gcd a b
  let b' := b / g
  b' - 1

#guard minOperations 2 4 = 1
#guard minOperations 4 10 = 4
#guard minOperations 1 4 = 3
