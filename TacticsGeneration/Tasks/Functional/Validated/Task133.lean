import Batteries

open Std

def sumNegativenum (nums : List Int) : Int :=
  let negNums := nums.filter (fun x => x < 0)
  negNums.foldl (fun acc x => acc + x) 0

#guard sumNegativenum [2, 4, -6, -9, 11, -12, 14, -5, 17] == -32
#guard sumNegativenum [10, 15, -14, 13, -18, 12, -20] == -52
#guard sumNegativenum [19, -65, 57, 39, 152, -639, 121, 44, 90, -190] == -894
