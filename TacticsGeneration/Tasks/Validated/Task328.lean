import Batteries

open Std

def rotateLeft (list1 : List Nat) (m n : Nat) : List Nat :=
  list1.drop m ++ list1.take n

#guard rotateLeft [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 3 4 = [4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4]
#guard rotateLeft [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 2 2 = [3, 4, 5, 6, 7, 8, 9, 10, 1, 2]
#guard rotateLeft [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 5 2 = [6, 7, 8, 9, 10, 1, 2]
