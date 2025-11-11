import Batteries

open Std

partial def zigzag (n k : Nat) : Nat :=
  if n == 0 && k == 0 then
    1
  else if k == 0 then
    0
  else
    zigzag n (k - 1) + zigzag (n - 1) (n - k)

#guard zigzag 4 3 = 5
#guard zigzag 4 2 = 4
#guard zigzag 3 1 = 1
