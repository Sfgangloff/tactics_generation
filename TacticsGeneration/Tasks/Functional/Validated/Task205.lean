import Batteries

open Std

def inversionElements (test_tup : List Int) : List Int :=
  let res := test_tup.map (fun x => -x - 1)
  res

#guard inversionElements [7, 8, 9, 1, 10, 7] = [-8, -9, -10, -2, -11, -8]
#guard inversionElements [2, 4, 5, 6, 1, 7] = [-3, -5, -6, -7, -2, -8]
#guard inversionElements [8, 9, 11, 14, 12, 13] = [-9, -10, -12, -15, -13, -14]
