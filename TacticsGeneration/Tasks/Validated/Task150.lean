import Batteries
open Std

def doesContainB (a b c : Int) : Bool :=
  if a == b then
    true
  else
    let diff := b - a
    if (decide ((diff * c) > 0)) && (diff % c == 0) then true else false

#guard doesContainB 1 7 3 == true
#guard doesContainB 1 (-3) 5 == false
#guard doesContainB 3 2 5 == false
