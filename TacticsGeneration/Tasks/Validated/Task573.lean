import Batteries

open Std

def unique_product (list_data : List Nat) : Nat := Id.run do
  let mut seen : HashSet Nat := {}
  let mut p := 1
  for i in list_data do
    if !seen.contains i then
      p := p * i
      seen := seen.insert i
  return p

#guard unique_product [10, 20, 30, 40, 20, 50, 60, 40] = 720000000
#guard unique_product [1, 2, 3, 1] = 6
#guard unique_product [7, 8, 9, 0, 1, 1] = 0
