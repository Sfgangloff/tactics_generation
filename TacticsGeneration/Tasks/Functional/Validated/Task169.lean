import Batteries

open Std

def getPell (n : Nat) : Nat := Id.run do
  if n <= 2 then
    return n
  let mut a := 1
  let mut b := 2
  for _ in [3 : n+1] do
    let c := 2 * b + a
    a := b
    b := c
  return b

#guard getPell 4 == 12
#guard getPell 7 == 169
#guard getPell 8 == 408
