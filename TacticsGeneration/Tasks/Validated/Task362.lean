import Batteries

open Std

def maxOccurrences (nums : List Nat) : Nat := Id.run do
  
  let mut maxVal : Nat := 0
  let mut result : Nat := match nums with
    | [] => 0
    | x :: _ => x
  for i in nums do
    let occu := nums.foldl (fun acc x => if x == i then acc + 1 else acc) 0
    if occu > maxVal then
      maxVal := occu
      result := i
  return result

#guard maxOccurrences [1,2,3,1,2,3,12,4,2] = 2
#guard maxOccurrences [1,2,6,7,0,1,0,1,0] = 1
#guard maxOccurrences [1,2,3,1,2,4,1] = 1
