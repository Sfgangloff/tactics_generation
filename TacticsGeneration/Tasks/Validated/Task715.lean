import Batteries

open Std

def strToTuple (test_str : String) : List Int :=
  test_str.splitOn ", " |>.map (fun s => (s.toInt?).getD 0)

#guard strToTuple "1, -5, 4, 6, 7" == [1, -5, 4, 6, 7]
#guard strToTuple "1, 2, 3, 4, 5" == [1, 2, 3, 4, 5]
#guard strToTuple "4, 6, 9, 11, 13, 14" == [4, 6, 9, 11, 13, 14]
