import Batteries

open Std

def countSamePair (nums1 nums2 : List Int) : Nat :=
  let eqs : List Bool := (List.zip nums1 nums2).map (fun (a, b) => a == b)
  eqs.foldl (fun acc b => acc + (if b then 1 else 0)) 0

#guard countSamePair [1, 2, 3, 4, 5, 6, 7, 8] [2, 2, 3, 1, 2, 6, 7, 9] = 4
#guard countSamePair [0, 1, 2, -1, -5, 6, 0, -3, -2, 3, 4, 6, 8] [2, 1, 2, -1, -5, 6, 4, -3, -2, 3, 4, 6, 8] = 11
#guard countSamePair [2, 4, -6, -9, 11, -12, 14, -5, 17] [2, 1, 2, -1, -5, 6, 4, -3, -2, 3, 4, 6, 8] = 1
