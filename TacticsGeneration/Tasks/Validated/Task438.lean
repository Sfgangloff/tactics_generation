import Batteries

open Std

def countBidirectional (testList : List (Nat × Nat)) : String := Id.run do
  let n := testList.length
  let mut res := 0
  for idx in [0 : n] do
    for iidx in [idx + 1 : n] do
      let a := testList.getD iidx (0, 0)
      let b := testList.getD idx (0, 0)
      if a.fst == b.snd && b.snd == a.fst then
        res := res + 1
  return toString res

#guard countBidirectional [(5, 6), (1, 2), (6, 5), (9, 1), (6, 5), (2, 1)] = "3"
#guard countBidirectional [(5, 6), (1, 3), (6, 5), (9, 1), (6, 5), (2, 1)] = "2"
#guard countBidirectional [(5, 6), (1, 2), (6, 5), (9, 2), (6, 5), (2, 1)] = "4"
