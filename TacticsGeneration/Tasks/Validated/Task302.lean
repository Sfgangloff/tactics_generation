import Batteries

open Std

def set_Bit_Number (n : Nat) : Nat := Id.run do
  if n == 0 then
    return 0
  let mut msb := 0
  let mut m := n / 2
  while m > 0 do
    m := m / 2
    msb := msb + 1
  return 2 ^ msb

#guard set_Bit_Number 6 = 4
#guard set_Bit_Number 10 = 8
#guard set_Bit_Number 18 = 16
