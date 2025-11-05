import Batteries

open Std

def len_log (list1 : List String) : Nat := Id.run do
  match list1 with
  | [] => return 0
  | x :: xs =>
    let mut mn := x.length
    for s in (x :: xs) do
      if s.length < mn then
        mn := s.length
    return mn

#guard len_log ["win","lose","great"] = 3
#guard len_log ["a","ab","abc"] = 1
#guard len_log ["12","12","1234"] = 2
