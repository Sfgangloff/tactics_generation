import Batteries

open Std

def addList (nums1 nums2 : List Nat) : List Nat :=
  (List.zip nums1 nums2).map (fun (p : Nat × Nat) => p.fst + p.snd)

#guard addList [1, 2, 3] [4, 5, 6] = [5, 7, 9]
#guard addList [1, 2] [3, 4] = [4, 6]
#guard addList [10, 20] [50, 70] = [60, 90]
