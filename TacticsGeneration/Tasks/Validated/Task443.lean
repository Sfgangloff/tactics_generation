import Batteries

open Std

def largest_neg (list1 : List Int) : Int := Id.run do
  let mut m := match list1 with
    | [] => 0
    | h :: _ => h
  for x in list1 do
    if x < m then
      m := x
  return m

#guard largest_neg ([1, 2, 3, -4, -6] : List Int) = -6
#guard largest_neg ([1, 2, 3, -8, -9] : List Int) = -9
#guard largest_neg ([1, 2, 3, 4, -1] : List Int) = -1
