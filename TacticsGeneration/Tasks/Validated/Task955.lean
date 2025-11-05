import Batteries

open Std

def isAbundant (n : Nat) : Bool := Id.run do
  let mut fctrsum := 0
  for fctr in [1 : n] do
    if n % fctr == 0 then
      fctrsum := fctrsum + fctr
  return fctrsum > n

#guard isAbundant 12 == true
#guard isAbundant 13 == false
#guard isAbundant 9 == false
