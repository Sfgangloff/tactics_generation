import Batteries

open Std

def perfectSquares (a b : Nat) : List Nat := Id.run do
  let mut lists : List Nat := []
  for i in [a : b+1] do
    for j in [1 : i+1] do
      if j * j == i then
        lists := lists ++ [i]
  return lists

#guard perfectSquares 1 30 == [1, 4, 9, 16, 25]
#guard perfectSquares 50 100 == [64, 81, 100]
#guard perfectSquares 100 200 == [100, 121, 144, 169, 196]
