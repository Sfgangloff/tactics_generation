import Batteries

open Std

def adjacentNumProduct (listNums : List Nat) : Nat := Id.run do
  match listNums with
  | [] => return 0  
  | [_] => return 0 
  | a :: b :: t =>
    let mut prev := b
    let mut best := a * b
    for x in t do
      let p := prev * x
      if p > best then
        best := p
      prev := x
    return best

#guard adjacentNumProduct [1, 2, 3, 4, 5, 6] = 30
#guard adjacentNumProduct [1, 2, 3, 4, 5] = 20
#guard adjacentNumProduct [2, 3] = 6
