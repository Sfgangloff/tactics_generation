import Batteries



/-!
  Auto-generated from task 6.
  Module: Task6
-/

open Std

def is_Power_Of_Two (x : Nat) : Bool := Id.run do
  if x == 0 then
    return false
  let mut a := x
  let mut b := x - 1
  let mut c := a &&& b
  if c == 0 then
    return true
  return false

def differ_At_One_Bit_Pos (a b : Nat) : Bool := Id.run do
  let mut x := a ^^^ b
  let mut res := is_Power_Of_Two x
  return res


-- Tests
#eval (differ_At_One_Bit_Pos 13 9) = true
#eval (differ_At_One_Bit_Pos 15 8) = false
#eval (differ_At_One_Bit_Pos 2 4) = false
