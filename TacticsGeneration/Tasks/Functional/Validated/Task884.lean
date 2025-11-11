import Batteries

open Std

def all_Bits_Set_In_The_Given_Range (n l r : Nat) : Bool :=
  let num := ((2 ^ r) - 1) ^^^ ((2 ^ (l - 1)) - 1)
  let new_num := n &&& num
  if num == new_num then
    true
  else
    false

#guard all_Bits_Set_In_The_Given_Range 10 2 1 == true
#guard all_Bits_Set_In_The_Given_Range 5 2 4 == false
#guard all_Bits_Set_In_The_Given_Range 22 2 3 == true
