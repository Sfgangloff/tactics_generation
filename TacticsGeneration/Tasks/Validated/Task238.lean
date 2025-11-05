import Batteries

open Std

def number_of_substrings (s : String) : Nat :=
  let str_len := s.length
  (str_len * (str_len + 1)) / 2

#guard number_of_substrings "abc" = 6
#guard number_of_substrings "abcd" = 10
#guard number_of_substrings "abcde" = 15
