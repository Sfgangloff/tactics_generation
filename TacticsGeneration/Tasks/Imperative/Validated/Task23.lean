import Batteries



/-!
  Auto-generated from task 23.
  Module: Task23
-/

open Std

def maximum_Sum (list1 : Array (Array Int)) : Int := Id.run do
  let mut maxi : Int := (-100000)
  for x in list1 do
    let mut s : Int := 0
    for y in x do
      s := s + y
    if s > maxi then
      maxi := s
  return maxi


-- Tests
#guard maximum_Sum (#[#[1,2,3], #[4,5,6], #[10,11,12], #[7,8,9]] : Array (Array Int)) == 33
#guard maximum_Sum (#[#[0,1,1], #[1,1,2], #[3,2,1]] : Array (Array Int)) == 6
#guard maximum_Sum (#[#[0,1,3], #[1,2,1], #[9,8,2], #[0,1,0], #[6,4,8]] : Array (Array Int)) == 19
#guard maximum_Sum (#[#[0,-1,-1], #[-1,-1,-2], #[-3,-2,-1]] : Array (Array Int)) == (-2)
