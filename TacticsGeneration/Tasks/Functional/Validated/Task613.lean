import Batteries

open Std

def maximumValue (testList : List (String × List Nat)) : List (String × Nat) :=
  testList.map (fun (key, lst) =>
    let m :=
      match lst with
      | [] => 0  
      | h :: t => t.foldl (fun acc x => if acc < x then x else acc) h
    (key, m)
  )

#guard maximumValue [("key1", [3, 4, 5]), ("key2", [1, 4, 2]), ("key3", [9, 3])] == [("key1", 5), ("key2", 4), ("key3", 9)]
#guard maximumValue [("key1", [4, 5, 6]), ("key2", [2, 5, 3]), ("key3", [10, 4])] == [("key1", 6), ("key2", 5), ("key3", 10)]
#guard maximumValue [("key1", [5, 6, 7]), ("key2", [3, 6, 4]), ("key3", [11, 5])] == [("key1", 7), ("key2", 6), ("key3", 11)]
