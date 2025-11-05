import Batteries

open Std

def isWoodall (x : Int) : Bool := Id.run do
  if x % 2 == 0 then
    return false
  if x == 1 then
    return true
  let mut x := x + 1
  let mut p := 0
  while x % 2 == 0 do
    x := x / 2
    p := p + 1
    if p == x then
      return true
  return false

#guard isWoodall 383 == true
#guard isWoodall 254 == false
#guard isWoodall 200 == false
#guard isWoodall 32212254719 == true
#guard isWoodall 32212254718 == false
#guard isWoodall 159 == true
