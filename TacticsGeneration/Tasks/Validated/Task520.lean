import Batteries
open Std

def findLcm (num1 num2 : Nat) : Nat := Id.run do
  let mut num := if num1 > num2 then num1 else num2
  let mut den := if num1 > num2 then num2 else num1
  
  let mut rem := num % den
  while rem != 0 do
    num := den
    den := rem
    rem := num % den
  let g := den
  let lcm := (num1 * num2) / g
  return lcm

def getLcm (l : List Nat) : Nat := Id.run do
  match l with
  | num1 :: num2 :: rest =>
    let mut lcm := findLcm num1 num2
    for v in rest do
      lcm := findLcm lcm v
    return lcm
  | _ => return 0

#guard getLcm [2, 7, 3, 9, 4] = 252
#guard getLcm [1, 2, 8, 3] = 24
#guard getLcm [3, 8, 4, 10, 5] = 120
