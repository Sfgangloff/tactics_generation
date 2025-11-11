import Batteries

open Std

def divList (nums1 : List Nat) (nums2 : List Nat) : List Float :=
  (List.zip nums1 nums2).map (fun p => (Float.ofNat p.fst) / (Float.ofNat p.snd))

#guard divList [4, 5, 6] [1, 2, 3] == [4.0, 2.5, 2.0]
#guard divList [3, 2] [1, 4] == [3.0, 0.5]
#guard divList [90, 120] [50, 70] == [1.8, 1.7142857142857142]
