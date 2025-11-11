import Batteries

open Std

def substractElements (testTup1 testTup2 : List Int) : List Int :=
  (List.zip testTup1 testTup2).map (fun (i, j) => i - j)

#guard substractElements ([10, 4, 5] : List Int) ([2, 5, 18] : List Int) == [8, -1, -13]
#guard substractElements ([11, 2, 3] : List Int) ([24, 45, 16] : List Int) == [-13, -43, -13]
#guard substractElements ([7, 18, 9] : List Int) ([10, 11, 12] : List Int) == [-3, 7, -3]
