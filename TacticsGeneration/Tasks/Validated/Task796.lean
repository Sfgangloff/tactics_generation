import Batteries

open Std

def returnSum (dict : HashMap String Nat) : Nat := Id.run do
  let mut s := 0
  for (_, v) in dict.toList do
    s := s + v
  return s

def buildDict (xs : List (String × Nat)) : HashMap String Nat := Id.run do
  let mut m : HashMap String Nat := {}
  for (k, v) in xs do
    m := m.insert k v
  return m

#guard returnSum (buildDict [("a", 100), ("b", 200), ("c", 300)]) = 600
#guard returnSum (buildDict [("a", 25), ("b", 18), ("c", 45)]) = 88
#guard returnSum (buildDict [("a", 36), ("b", 39), ("c", 49)]) = 124
