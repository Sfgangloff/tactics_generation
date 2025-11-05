import Batteries

open Std

def sumPositivenum (nums : List Int) : Int :=
  let sum_positivenum := nums.filter (fun nums => nums > 0)
  sum_positivenum.foldl (fun acc x => acc + x) 0

#guard sumPositivenum [2, 4, -6, -9, 11, -12, 14, -5, 17] = 48
#guard sumPositivenum [10, 15, -14, 13, -18, 12, -20] = 50
#guard sumPositivenum [19, -65, 57, 39, 152, -639, 121, 44, 90, -190] = 522
