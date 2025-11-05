import Batteries

open Std

def rotateRight (list1 : List Nat) (m n : Nat) : List Nat :=
  let len := list1.length
  let lastM :=
    if m == 0 then
      list1
    else if len ≤ m then
      list1
    else
      list1.drop (len - m)
  let firstWithoutLastN :=
    if n == 0 then
      []
    else if len ≤ n then
      []
    else
      list1.take (len - n)
  lastM ++ firstWithoutLastN

#guard rotateRight [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 3 4 == [8, 9, 10, 1, 2, 3, 4, 5, 6]
#guard rotateRight [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 2 2 == [9, 10, 1, 2, 3, 4, 5, 6, 7, 8]
#guard rotateRight [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 5 2 == [6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8]
