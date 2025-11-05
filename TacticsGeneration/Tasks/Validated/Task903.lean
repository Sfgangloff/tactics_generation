import Batteries

open Std

def countUnsetBits (n : Nat) : Nat := Id.run do
  let mut cnt := 0
  for i in [1 : n + 1] do
    let mut temp := i
    while temp != 0 do
      if temp % 2 == 0 then
        cnt := cnt + 1
      temp := temp / 2
  return cnt

#guard countUnsetBits 2 == 1
#guard countUnsetBits 5 == 4
#guard countUnsetBits 14 == 17
