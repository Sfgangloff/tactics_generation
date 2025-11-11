import Batteries

open Std

def checkEvenParity (x : Nat) : Bool := Id.run do
  let mut x := x
  let mut parity := 0
  while x != 0 do
    x := x &&& (x - 1)
    parity := parity + 1
  if parity % 2 == 0 then
    return true
  else
    return false

#guard checkEvenParity 10 == true
#guard checkEvenParity 11 == false
#guard checkEvenParity 18 == true
