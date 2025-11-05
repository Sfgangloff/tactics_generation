import Batteries
open Std

def nthIntD (xs : List Int) (i : Nat) (d : Int) : Int :=
  match xs, i with
  | [], _ => d
  | x :: _, 0 => x
  | _ :: xs', Nat.succ j => nthIntD xs' j d

def max_sub_array_sum (a : List Int) (size : Nat) : Nat := Id.run do
  
  let mut max_so_far : Int := -1000000000000000000
  let mut max_ending_here : Int := 0
  let mut start : Nat := 0
  let mut endIdx : Nat := 0
  let mut s : Nat := 0
  for i in [0 : size] do
    let v := nthIntD a i 0
    max_ending_here := max_ending_here + v
    if max_so_far < max_ending_here then
      max_so_far := max_ending_here
      start := s
      endIdx := i
    if max_ending_here < 0 then
      max_ending_here := 0
      s := i + 1
  return endIdx - start + 1

#guard max_sub_array_sum [-2, -3, 4, -1, -2, 1, 5, -3] 8 = 5
#guard max_sub_array_sum [1, -2, 1, 1, -2, 1] 6 = 2
#guard max_sub_array_sum [-1, -2, 3, 4, 5] 5 = 3
