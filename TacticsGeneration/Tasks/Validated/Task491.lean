import Batteries

open Std

def sumGp (a n r : Nat) : Nat := Id.run do
  let mut total := 0
  let mut term := a
  for _ in [: n] do
    total := total + term
    term := term * r
  return total

#guard sumGp 1 5 2 = 31
#guard sumGp 1 5 4 = 341
#guard sumGp 2 6 3 = 728
