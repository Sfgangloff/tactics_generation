import Batteries

open Std

def countUnsetBits (n : Nat) : Nat := Id.run do
  let mut count := 0
  let mut x := 1
  while x < n + 1 do
    if (x &&& n) == 0 then
      count := count + 1
    x := x <<< 1
  return count

#guard countUnsetBits 2 = 1
#guard countUnsetBits 4 = 2
#guard countUnsetBits 6 = 1
