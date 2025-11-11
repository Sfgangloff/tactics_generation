import Batteries

open Std

def sub_list (nums1 nums2 : List Int) : List Int :=
  List.zipWith (fun x y => x - y) nums1 nums2

#guard sub_list [1, 2, 3] [4, 5, 6] == [-3, -3, -3]
#guard sub_list [1, 2] [3, 4] == [-2, -2]
#guard sub_list [90, 120] [50, 70] == [40, 50]
