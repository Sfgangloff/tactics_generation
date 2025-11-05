import Batteries

open Std

def get_odd_occurence (arr : List Int) (arr_size : Nat) : Int := Id.run do
  
  let a := arr.toArray
  for i in [0 : arr_size] do
    let ai := a[i]!
    let mut count : Nat := 0
    for j in [0 : arr_size] do
      if ai == a[j]! then
        count := count + 1
    if count % 2 != 0 then
      return ai
  return (-1 : Int)

#guard get_odd_occurence ([2, 3, 5, 4, 5, 2, 4, 3, 5, 2, 4, 4, 2] : List Int) 13 = 5
#guard get_odd_occurence ([1, 2, 3, 2, 3, 1, 3] : List Int) 7 = 3
#guard get_odd_occurence ([5, 7, 2, 7, 5, 2, 5] : List Int) 7 = 5
