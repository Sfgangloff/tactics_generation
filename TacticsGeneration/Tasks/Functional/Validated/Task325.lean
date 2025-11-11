import Batteries

open Std

partial def get_Min_Squares (n : Nat) : Nat :=
  if n ≤ 3 then n else Id.run do
    let mut res := n
    for x in [1 : n + 1] do
      let temp := x * x
      if temp > n then
        break
      else
        res := Nat.min res (1 + get_Min_Squares (n - temp))
    return res

#guard get_Min_Squares 6 = 3
#guard get_Min_Squares 2 = 2
#guard get_Min_Squares 4 = 1
