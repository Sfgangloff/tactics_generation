import Batteries

open Std

def modularInverse (arr : List Nat) (N P : Nat) : Nat := Id.run do
  
  let arrA := arr.toArray
  let mut currentElement := 0
  for i in [0 : N] do
    let x := arrA[i]!
    if (x * x) % P == 1 then
      currentElement := currentElement + 1
  return currentElement

#guard modularInverse [1, 6, 4, 5] 4 7 = 2
#guard modularInverse [1, 3, 8, 12, 12] 5 13 = 3
#guard modularInverse [2, 3, 4, 5] 4 6 = 1
