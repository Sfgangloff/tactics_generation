import Batteries

open Std

def validate (n : Nat) : Bool := Id.run do
  for i in [0:10] do
    let mut temp := n
    let mut count := 0
    while temp != 0 do
      if temp % 10 == i then
        count := count + 1
      if Nat.blt i count then
        return false
      temp := temp / 10
  return true

#guard validate 1234 == true
#guard validate 51241 == false
#guard validate 321 == true
