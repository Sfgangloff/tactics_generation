import Batteries

open Std

def minProductTuple (list1 : List (Nat × Nat)) : Nat :=
  match list1 with
  | [] => 0  
  | (x, y) :: xs =>
    let init := x * y
    xs.foldl (fun acc p =>
      let v := p.fst * p.snd
      if v < acc then v else acc) init

#guard minProductTuple [(2, 7), (2, 6), (1, 8), (4, 9)] = 8
#guard minProductTuple [(10, 20), (15, 2), (5, 10)] = 30
#guard minProductTuple [(11, 44), (10, 15), (20, 5), (12, 9)] = 100
