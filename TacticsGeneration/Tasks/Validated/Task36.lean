import Batteries

open Std

def findNthDigit (p q N : Nat) : Nat := Id.run do
  let mut p := p
  let mut N := N
  let mut res := 0
  while N > 0 do
    N := N - 1
    p := p * 10
    res := p / q
    p := p % q
  return res

#guard findNthDigit 1 2 1 == 5
#guard findNthDigit 3 5 1 == 6
#guard findNthDigit 5 6 5 == 3
