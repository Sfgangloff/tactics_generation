import Batteries

open Std

def add_K_element (test_list : List (List Nat)) (K : Nat) : List (List Nat) :=
  test_list.map (fun sub => sub.map (fun j => j + K))

#guard add_K_element [[1, 3, 4], [2, 4, 6], [3, 8, 1]] 4 == [[5, 7, 8], [6, 8, 10], [7, 12, 5]]
#guard add_K_element [[1, 2, 3], [4, 5, 6], [7, 8, 9]] 8 == [[9, 10, 11], [12, 13, 14], [15, 16, 17]]
#guard add_K_element [[11, 12, 13], [14, 15, 16], [17, 18, 19]] 9 == [[20, 21, 22], [23, 24, 25], [26, 27, 28]]
