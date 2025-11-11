import Batteries

open Std

def frequencyOfSmallest (n : Nat) (arr : List Nat) : Nat := Id.run do
  
  
  let a := arr.toArray
  let mut mn := a[0]!
  let mut freq : Nat := 1
  for i in [1 : n] do
    let x := a[i]!
    if x < mn then
      mn := x
      freq := 1
    else if x = mn then
      freq := freq + 1
    else
      pure ()
  return freq

#guard frequencyOfSmallest 5 [1, 2, 3, 4, 3] = 1
#guard frequencyOfSmallest 7 [3, 1, 2, 5, 6, 2, 3] = 1
#guard frequencyOfSmallest 7 [3, 3, 6, 3, 7, 4, 9] = 3
