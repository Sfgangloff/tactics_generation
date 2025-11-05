import Batteries

open Std

def mutiple_tuple (nums : List Int) : Int := Id.run do
  let temp := nums
  let mut product : Int := 1
  for x in temp do
    product := product * x
  return product

#guard mutiple_tuple [4, 3, 2, 2, -1, 18] = -864
#guard mutiple_tuple [1, 2, 3] = 6
#guard mutiple_tuple [-2, -4, -6] = -48
