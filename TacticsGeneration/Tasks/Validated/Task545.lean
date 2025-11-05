import Batteries

open Std

def take_L_and_F_set_bits (n : Nat) : Nat := Id.run do
  let mut m := n
  m := m ||| Nat.shiftRight m 1
  m := m ||| Nat.shiftRight m 2
  m := m ||| Nat.shiftRight m 4
  m := m ||| Nat.shiftRight m 8
  m := m ||| Nat.shiftRight m 16
  return (Nat.shiftRight (m + 1) 1) + 1

def toggle_F_and_L_bits (n : Nat) : Nat :=
  if n == 1 then 0 else n ^^^ take_L_and_F_set_bits n

#guard toggle_F_and_L_bits 10 == 3
#guard toggle_F_and_L_bits 15 == 6
#guard toggle_F_and_L_bits 20 == 5
