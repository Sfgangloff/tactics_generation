import Batteries



/-!
  Auto-generated from task 20.
  Module: Task20
-/

open Std

def is_woodall (x : Nat) : Bool := Id.run do
  if x % 2 == 0 then
    return false
  if x == 1 then
    return true
  let mut x := x + 1
  let mut p := 0
  -- The loop will run at most 'limit' times, but will break as soon as x becomes odd
  let limit := x
  for _ in [:limit] do
    if x % 2 == 0 then
      x := x / 2
      p := p + 1
      if p == x then
        return true
    else
      break
  return false


-- Tests
#guard is_woodall 383 = true
#guard is_woodall 254 = false
#guard is_woodall 200 = false
#guard is_woodall 32212254719 = true
#guard is_woodall 32212254718 = false
#guard is_woodall 159 = true
