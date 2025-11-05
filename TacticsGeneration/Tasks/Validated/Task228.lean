import Batteries

open Std

def all_Bits_Set_In_The_Given_Range (n l r : Nat) : Bool :=
  let num := (((Nat.shiftLeft 1 r) - 1) ^^^ ((Nat.shiftLeft 1 (l - 1)) - 1))
  let new_num := n &&& num
  if new_num == 0 then true else false

#guard all_Bits_Set_In_The_Given_Range 4 1 2 == true
#guard all_Bits_Set_In_The_Given_Range 17 2 4 == true
#guard all_Bits_Set_In_The_Given_Range 39 4 6 == false
