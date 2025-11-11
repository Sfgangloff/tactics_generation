import Batteries

open Std

def prodSquare (n : Nat) : Bool := Id.run do
  for i in [2 : n + 1] do
    if i * i < n + 1 then
      for j in [2 : n + 1] do
        if i * i * j * j == n then
          return true
  return false

#guard prodSquare 25 == false
#guard prodSquare 30 == false
#guard prodSquare 16 == true
