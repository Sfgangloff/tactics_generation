import Batteries

open Std

def count_Hexadecimal (L R : Nat) : Nat := Id.run do
  let mut count := 0
  for i in [L : R+1] do
    if h15 : i ≤ 15 then
      if h10 : 10 ≤ i then
        count := count + 1
      else
        pure ()
    else
      let mut k := i
      while k != 0 do
        if hDigit : 10 ≤ k % 16 then
          count := count + 1
        else
          pure ()
        k := k / 16
  return count

#guard count_Hexadecimal 10 15 = 6
#guard count_Hexadecimal 2 4 = 0
#guard count_Hexadecimal 15 16 = 1
