import Batteries

open Std

partial def binomialCoeffi (n k : Nat) : Nat :=
  if k == 0 || k == n then
    1
  else
    binomialCoeffi (n - 1) (k - 1) + binomialCoeffi (n - 1) k

partial def rencontresNumber (n m : Nat) : Nat :=
  if n == 0 && m == 0 then
    1
  else if n == 1 && m == 0 then
    0
  else if m == 0 then
    (n - 1) * (rencontresNumber (n - 1) 0 + rencontresNumber (n - 2) 0)
  else
    binomialCoeffi n m * rencontresNumber (n - m) 0

#guard rencontresNumber 7 2 = 924
#guard rencontresNumber 3 0 = 2
#guard rencontresNumber 3 1 = 3
