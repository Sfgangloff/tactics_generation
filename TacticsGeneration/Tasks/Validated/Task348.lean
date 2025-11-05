import Batteries

open Std

def binCoff (n r : Nat) : Nat := Id.run do
  let mut val := 1
  let mut r' := r
  if r' > n - r' then
    r' := n - r'
  for i in [: r'] do
    val := val * (n - i)
    val := val / (i + 1)
  return val

def findWays (M : Nat) : Nat :=
  let n := M / 2
  let a := binCoff (2 * n) n
  let b := a / (n + 1)
  b

#guard findWays 4 = 2
#guard findWays 6 = 5
#guard findWays 8 = 14
