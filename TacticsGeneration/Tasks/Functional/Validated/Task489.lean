import Batteries

open Std

def frequency_Of_Largest (n : Nat) (arr : List Nat) : Nat := Id.run do
  let a := arr.toArray
  let mut mn := a[0]!
  let mut freq := 1
  for i in [1 : n] do
    let v := a[i]!
    if v > mn then
      mn := v
      freq := 1
    else if v == mn then
      freq := freq + 1
    else
      ()
  return freq

#guard frequency_Of_Largest 5 [1,2,3,4,4] = 2
#guard frequency_Of_Largest 3 [5,6,5] = 1
#guard frequency_Of_Largest 4 [2,7,7,7] = 3
