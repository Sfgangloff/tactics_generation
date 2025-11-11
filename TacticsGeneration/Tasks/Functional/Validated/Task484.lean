import Batteries

open Std

def removeMatchingTuple (test_list1 test_list2 : List (String × String)) : List (String × String) :=
  test_list1.filter (fun sub => !(test_list2.contains sub))

#guard removeMatchingTuple [("Hello", "dude"), ("How", "are"), ("you", "?")] [("Hello", "dude"), ("How", "are")] = [("you", "?")]
#guard removeMatchingTuple [("Part", "of"), ("the", "journey"), ("is ", "end")] [("Journey", "the"), ("is", "end")] = [("Part", "of"), ("the", "journey"), ("is ", "end")]
#guard removeMatchingTuple [("Its", "been"), ("a", "long"), ("day", "without")] [("a", "long"), ("my", "friend")] = [("Its", "been"), ("day", "without")]
