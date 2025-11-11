import Batteries

open Std

def maximumSum (list1 : List (List Int)) : Int :=
  list1.foldl (fun maxi x =>
    let sum := x.foldl (fun acc y => acc + y) 0
    if sum > maxi then sum else maxi
  ) (-100000)

#guard maximumSum [[1,2,3],[4,5,6],[10,11,12],[7,8,9]] == 33
#guard maximumSum [[0,1,1],[1,1,2],[3,2,1]] == 6
#guard maximumSum [[0,1,3],[1,2,1],[9,8,2],[0,1,0],[6,4,8]] == 19
#guard maximumSum [[0,-1,-1],[-1,-1,-2],[-3,-2,-1]] == -2
