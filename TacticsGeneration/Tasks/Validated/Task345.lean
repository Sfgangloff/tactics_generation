import Batteries

open Std

def diffConsecutivenums (nums : List Int) : List Int :=
  match nums with
  | a :: b :: t => (b - a) :: diffConsecutivenums (b :: t)
  | _ => []

#guard diffConsecutivenums [1, 1, 3, 4, 4, 5, 6, 7] == [0, 2, 1, 0, 1, 1, 1]
#guard diffConsecutivenums [4, 5, 8, 9, 6, 10] == [1, 3, 1, -3, 4]
#guard diffConsecutivenums [0, 1, 2, 3, 4, 4, 4, 4, 5, 7] == [1, 1, 1, 1, 0, 0, 0, 1, 2]
