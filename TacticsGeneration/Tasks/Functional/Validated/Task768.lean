import Batteries

open Std

def check_Odd_Parity (x : Nat) : Bool := Id.run do
  let mut x := x
  let mut parity : Nat := 0
  while x != 0 do
    x := x &&& (x - 1)
    parity := parity + 1
  return parity % 2 == 1

#guard check_Odd_Parity 13 == true
#guard check_Odd_Parity 21 == true
#guard check_Odd_Parity 18 == false
