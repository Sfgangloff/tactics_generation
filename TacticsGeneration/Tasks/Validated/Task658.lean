import Batteries

open Std

def countOcc (xs : List Nat) (x : Nat) : Nat :=
  xs.foldl (fun acc y => if y == x then acc + 1 else acc) 0

def maxOccurrences (list1 : List Nat) : Nat := Id.run do
  let result0 := match list1 with
    | [] => 0
    | x :: _ => x
  let mut maxVal := 0
  let mut result := result0
  for i in list1 do
    let occu := countOcc list1 i
    if occu > maxVal then
      maxVal := occu
      result := i
  return result

#guard maxOccurrences [2,3,8,4,7,9,8,2,6,5,1,6,1,2,3,4,6,9,1,2] = 2
#guard maxOccurrences [1, 3,5, 7,1, 3,13, 15, 17,5, 7,9,1, 11] = 1
#guard maxOccurrences [1, 2, 3,2, 4, 5,1, 1, 1] = 1
