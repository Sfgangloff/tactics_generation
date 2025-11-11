import Batteries

open Std

def firstDigit (n : Nat) : Nat := Id.run do
  let mut fact := 1
  for i in [2 : n+1] do
    fact := fact * i
    while fact % 10 == 0 do
      fact := fact / 10
  while !((fact / 10) == 0) do
    fact := fact / 10
  return fact

#guard firstDigit 5 = 1
#guard firstDigit 10 = 3
#guard firstDigit 7 = 5
