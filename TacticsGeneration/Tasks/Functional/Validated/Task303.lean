import Batteries

open Std

def solve (a : List Int) (n : Nat) : Bool := Id.run do
  let mut mx : Int := 0
  for j in [1 : n] do
    if j == 1 then
      
      mx := a.getD 0 0
    else
      let aj := a.getD j 0
      if mx > aj then
        return false
      let prev := a.getD (j-1) 0
      mx := if mx > prev then mx else prev
  return true

#guard solve [1, 0, 2] 3 == true
#guard solve [1, 2, 0] 3 == false
#guard solve [1, 2, 1] 3 == true
