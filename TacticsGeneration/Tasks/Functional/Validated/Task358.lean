import Batteries

open Std

def moddiv_list (nums1 nums2 : List Nat) : List Nat :=
  (List.zip nums1 nums2).map (fun (x, y) => x % y)

#guard moddiv_list [4,5,6] [1, 2, 3] == [0, 1, 0]
#guard moddiv_list [3,2] [1,4] == [0, 2]
#guard moddiv_list [90,120] [50,70] == [40, 50]
