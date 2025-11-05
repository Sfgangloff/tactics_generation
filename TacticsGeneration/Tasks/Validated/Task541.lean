import Batteries

open Std

def getSum (n : Nat) : Nat := Id.run do
  let bound := Nat.sqrt n
  let mut s : Nat := 0
  for i in [1 : bound + 1] do
    if n % i == 0 then
      let q := n / i
      if q == i then
        s := s + i
      else
        s := s + i
        s := s + q
  s := s - n
  return s

def checkAbundant (n : Nat) : Bool :=
  if getSum n > n then true else false

#guard checkAbundant 12 == true
#guard checkAbundant 15 == false
#guard checkAbundant 18 == true
