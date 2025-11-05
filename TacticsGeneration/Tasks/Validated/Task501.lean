import Batteries

open Std

def ngcd (x y : Nat) : Nat := Id.run do
  let m := Nat.min x y
  let mut g := 1
  for i in [1 : m + 1] do
    if x % i == 0 && y % i == 0 then
      g := i
  return g

def num_comm_div (x y : Nat) : Nat := Id.run do
  let n := ngcd x y
  let z := Nat.sqrt n
  let mut result := 0
  for i in [1 : z + 1] do
    if n % i == 0 then
      result := result + 2
      if i == n / i then
        result := result - 1
  return result

#guard num_comm_div 2 4 = 2
#guard num_comm_div 2 8 = 2
#guard num_comm_div 12 24 = 6
