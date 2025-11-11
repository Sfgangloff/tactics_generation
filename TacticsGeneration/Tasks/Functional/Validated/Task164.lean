import Batteries

open Std

def divSum (n : Nat) : Nat := Id.run do
  let mut s := 1
  for i in [2 : Nat.sqrt n + 1] do
    if n % i == 0 then
      s := s + i + n / i
  return s

def areEquivalent (num1 num2 : Nat) : Bool :=
  divSum num1 == divSum num2

#guard areEquivalent 36 57 == false
#guard areEquivalent 2 4 == false
#guard areEquivalent 23 47 == true
