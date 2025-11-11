import Batteries

open Std

def parallel_lines (line1 : List Int) (line2 : List Int) : Bool :=
  match line1, line2 with
  | a1 :: b1 :: _, a2 :: b2 :: _ => a1 * b2 == a2 * b1
  | _, _ => false

#guard parallel_lines [2,3,4] [2,3,8] == true
#guard parallel_lines [2,3,4] [4,-3,8] == false
#guard parallel_lines [3,3] [5,5] == true
