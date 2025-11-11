import Batteries

open Std

partial def sequence (n : Nat) : Nat :=
  if n == 1 || n == 2 then
    1
  else
    let prev := sequence (n - 1)
    sequence prev + sequence (n - prev)

#guard sequence 10 = 6
#guard sequence 2 = 1
#guard sequence 3 = 2
