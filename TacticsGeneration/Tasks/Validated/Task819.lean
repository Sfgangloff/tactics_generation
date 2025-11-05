import Batteries

open Std

def countDuplic (lists : List Nat) : (List Nat × List Nat) := Id.run do
  let mut element : List Nat := []
  let mut frequency : List Nat := []
  match lists with
  | [] => return (element, frequency)
  | prev :: tail =>
    let mut running := 1
    let mut cur := prev
    for x in tail do
      if cur == x then
        running := running + 1
      else
        frequency := frequency ++ [running]
        element := element ++ [cur]
        running := 1
        cur := x
    frequency := frequency ++ [running]
    element := element ++ [cur]
    return (element, frequency)

#guard countDuplic [1,2,2,2,4,4,4,5,5,5,5] == ([1, 2, 4, 5], [1, 3, 3, 4])
#guard countDuplic [2,2,3,1,2,6,7,9] == ([2, 3, 1, 2, 6, 7, 9], [2, 1, 1, 1, 1, 1, 1])
#guard countDuplic [2,1,5,6,8,3,4,9,10,11,8,12] == ([2, 1, 5, 6, 8, 3, 4, 9, 10, 11, 8, 12], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])
