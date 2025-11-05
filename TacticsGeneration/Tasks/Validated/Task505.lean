import Batteries

open Std

def re_order (A : List Nat) : List Nat := Id.run do
  let mut arr := A.toArray
  let mut k : Nat := 0
  
  for x in A do
    if x != 0 then
      arr := arr.set! k x
      k := k + 1
  
  for i in [k : arr.size] do
    arr := arr.set! i 0
  return arr.toList

#guard re_order [6, 0, 8, 2, 3, 0, 4, 0, 1] = [6, 8, 2, 3, 4, 1, 0, 0, 0]
#guard re_order [4, 0, 2, 7, 0, 9, 0, 12, 0] = [4, 2, 7, 9, 12, 0, 0, 0, 0]
#guard re_order [3, 11, 0, 74, 14, 0, 1, 0, 2] = [3, 11, 74, 14, 1, 2, 0, 0, 0]
