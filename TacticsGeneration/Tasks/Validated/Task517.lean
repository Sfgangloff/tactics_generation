import Batteries

open Std

def largestPos (list1 : List Int) : Int :=
  match list1 with
  | [] => 0
  | h :: _ =>
    Id.run do
      let mut m := h
      for x in list1 do
        if x > m then
          m := x
      return m

#guard largestPos [1, 2, 3, 4, -1] = 4
#guard largestPos [0, 1, 2, -5, -1, 6] = 6
#guard largestPos [0, 0, 1, 0] = 1
