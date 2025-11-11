import Batteries

open Std

def findRemainder (arr : List Nat) (lens : Nat) (n : Nat) : Nat := Id.run do
  
  let mut mul := 1
  for i in [: lens] do
    let ai := arr.getD i 0
    mul := (mul * (ai % n)) % n
  return mul % n

#guard findRemainder [100, 10, 5, 25, 35, 14] 6 11 = 9
#guard findRemainder [1, 1, 1] 3 1 = 0
#guard findRemainder [1, 2, 1] 3 2 = 0
