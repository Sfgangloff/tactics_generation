import Batteries

open Std

def newTuple (test_list : List String) (test_str : String) : List String :=
  let res := test_list ++ [test_str]
  res

#guard newTuple ["WEB", "is"] "best" == ["WEB", "is", "best"]
#guard newTuple ["We", "are"] "Developers" == ["We", "are", "Developers"]
#guard newTuple ["Part", "is"] "Wrong" == ["Part", "is", "Wrong"]
