import Batteries

open Std

def lastDigitFactorial (n : Nat) : Nat :=
  if n == 0 then 1
  else if n ≤ 2 then n
  else if n == 3 then 6
  else if n == 4 then 4
  else 0

#guard lastDigitFactorial 4 = 4
#guard lastDigitFactorial 21 = 0
#guard lastDigitFactorial 30 = 0
