import Batteries

open Std

def remove_kth_element (list1 : List Nat) (L : Nat) : List Nat :=
  list1.take (L - 1) ++ list1.drop L

#guard remove_kth_element [1,1,2,3,4,4,5,1] 3 = [1, 1, 3, 4, 4, 5, 1]
#guard remove_kth_element [0, 0, 1, 2, 3, 4, 4, 5, 6, 6, 6, 7, 8, 9, 4, 4] 4 = [0, 0, 1, 3, 4, 4, 5, 6, 6, 6, 7, 8, 9, 4, 4]
#guard remove_kth_element [10, 10, 15, 19, 18, 18, 17, 26, 26, 17, 18, 10] 5 = [10,10,15,19, 18, 17, 26, 26, 17, 18, 10]
