import Batteries

open Std

def mulList (nums1 nums2 : List Nat) : List Nat :=
  match nums1, nums2 with
  | x :: xs, y :: ys => (x * y) :: mulList xs ys
  | _, _ => []

#guard mulList [1, 2, 3] [4, 5, 6] = [4, 10, 18]
#guard mulList [1, 2] [3, 4] = [3, 8]
#guard mulList [90, 120] [50, 70] = [4500, 8400]
