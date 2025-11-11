import Batteries

open Std

def max_sub_array_sum (a : List Int) (size : Nat) : Int := Id.run do
  
  let arr := a.toArray
  let mut max_so_far : Int := 0
  let mut max_ending_here : Int := 0
  for i in [0 : size] do
    let x := arr[i]!
    max_ending_here := max_ending_here + x
    if max_ending_here < 0 then
      max_ending_here := 0
    else if max_so_far < max_ending_here then
      max_so_far := max_ending_here
  return max_so_far

#guard max_sub_array_sum [-2, -3, 4, -1, -2, 1, 5, -3] 8 = 7
#guard max_sub_array_sum [-3, -4, 5, -2, -3, 2, 6, -4] 8 = 8
#guard max_sub_array_sum [-4, -5, 6, -3, -4, 3, 7, -5] 8 = 10
