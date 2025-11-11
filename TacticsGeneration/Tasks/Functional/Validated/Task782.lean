import Batteries

open Std

def Odd_Length_Sum (arr : List Nat) : Nat := Id.run do
  let l := arr.length
  let mut s := 0
  for i in [0:l] do
    let coeff := (((i + 1) * (l - i) + 1) / 2)
    s := s + coeff * (arr.getD i 0)
  return s

#guard Odd_Length_Sum [1, 2, 4] = 14
#guard Odd_Length_Sum [1, 2, 1, 2] = 15
#guard Odd_Length_Sum [1, 7] = 8
