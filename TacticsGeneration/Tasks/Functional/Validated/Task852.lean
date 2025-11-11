import Batteries

open Std

def removeFirst (l : List Int) (x : Int) : List Int :=
  match l with
  | [] => []
  | y :: ys => if y == x then ys else y :: removeFirst ys x

def removeNegs (num_list : List Int) : List Int := Id.run do
  let mut curr := num_list
  for item in num_list do
    if item < 0 then
      curr := removeFirst curr item
    else
      ()
  return curr

#guard removeNegs [1, -2, 3, -4] = [1, 3]
#guard removeNegs [1, 2, 3, -4] = [1, 2, 3]
#guard removeNegs [4, 5, -6, 7, -8] = [4, 5, 7]
