import Batteries

open Std

def lcm (x y : Nat) : Nat :=
  
  let z0 := if x > y then x else y
  let rec loop (z remaining : Nat) : Nat :=
    match remaining with
    | 0 => z
    | Nat.succ r =>
      if z % x == 0 && z % y == 0 then z
      else loop (z+1) r
  loop z0 (x * y + 1)

#guard lcm 4 6 = 12
#guard lcm 15 17 = 255
#guard lcm 2 6 = 6
