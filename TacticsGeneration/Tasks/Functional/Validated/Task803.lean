import Batteries

open Std

def is_Perfect_Square (n : Nat) : Bool := Id.run do
  let mut i := 1
  while i * i <= n do
    if (n % i == 0) && (n / i == i) then
      return true
    i := i + 1
  return false

#guard is_Perfect_Square 10 == false
#guard is_Perfect_Square 36 == true
#guard is_Perfect_Square 14 == false
