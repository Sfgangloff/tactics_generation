import Batteries

open Std

def addConsecutiveNums (nums : List Nat) : List Nat :=
  match nums with
  | [] => []
  | [_] => []
  | a :: b :: t => (a + b) :: addConsecutiveNums (b :: t)

#guard addConsecutiveNums [1, 1, 3, 4, 4, 5, 6, 7] = [2, 4, 7, 8, 9, 11, 13]
#guard addConsecutiveNums [4, 5, 8, 9, 6, 10] = [9, 13, 17, 15, 16]
#guard addConsecutiveNums [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] = [3, 5, 7, 9, 11, 13, 15, 17, 19]
