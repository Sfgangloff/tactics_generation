import Batteries

open Std

partial def fibonacci (n : Nat) : Nat :=
  if n == 1 || n == 2 then 1
  else fibonacci (n - 1) + fibonacci (n - 2)

#guard fibonacci 7 = 13
#guard fibonacci 8 = 21
#guard fibonacci 9 = 34
