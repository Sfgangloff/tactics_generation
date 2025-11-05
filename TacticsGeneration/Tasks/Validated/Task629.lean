import Batteries

open Std

def Split (list : List Nat) : List Nat := Id.run do
  let mut ev_li : List Nat := []
  for i in list do
    if i % 2 == 0 then
      ev_li := ev_li ++ [i]
  return ev_li

#guard Split [1,2,3,4,5] = [2,4]
#guard Split [4,5,6,7,8,0,1] = [4,6,8,0]
#guard Split [8,12,15,19] = [8,12]
