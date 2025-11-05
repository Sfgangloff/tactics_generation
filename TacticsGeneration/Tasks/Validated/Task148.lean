import Batteries

open Std

def sumDigitsSingle (x : Nat) : Nat := Id.run do
  let mut ans := 0
  let mut y := x
  while y != 0 do
    ans := ans + y % 10
    y := y / 10
  return ans

def closest (x : Nat) : Nat := Id.run do
  let mut ans := 0
  while ans * 10 + 9 ≤ x do
    ans := ans * 10 + 9
  return ans

def sumDigitsTwoparts (N : Nat) : Nat :=
  let A := closest N
  sumDigitsSingle A + sumDigitsSingle (N - A)

#guard sumDigitsTwoparts 35 == 17
#guard sumDigitsTwoparts 7 == 7
#guard sumDigitsTwoparts 100 == 19
