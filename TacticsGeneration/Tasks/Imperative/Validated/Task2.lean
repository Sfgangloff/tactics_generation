import Batteries



/-!
  Auto-generated from task 2.
  Module: Task2
-/

open Std

namespace Task2

-- Build the intersection of two tuples (arrays) as a HashSet (set semantics)
-- Python behavior used sets; order is unspecified, so we return a HashSet Nat.
def similar_elements (test_tup1 : Array Nat) (test_tup2 : Array Nat) : Std.HashSet Nat := Id.run do
  let mut s1 : Std.HashSet Nat := {}
  for x in test_tup1 do
    s1 := s1.insert x
  let mut res : Std.HashSet Nat := Std.HashSet.empty
  for y in test_tup2 do
    if s1.contains y then
      res := res.insert y
  return res

-- Helper for tests: assert two HashSets are equal (unordered equality)
def assertHashSetEq (a b : Std.HashSet Nat) : Unit := Id.run do
  if a.size != b.size then
    panic! "HashSet size mismatch"
  for x in a do
    if ! b.contains x then
      panic! "Element missing in expected set"
  for x in b do
    if ! a.contains x then
      panic! "Element missing in actual set"
  return ()

end Task2


-- Tests
open Std
open Task2

-- Tests adapted to set semantics (unordered): compare as HashSets
def tests : Unit := Id.run do
  let r1 := similar_elements #[3, 4, 5, 6] #[5, 7, 4, 10]
  assertHashSetEq r1 (Std.HashSet.ofList [4, 5])
  let r2 := similar_elements #[1, 2, 3, 4] #[5, 4, 3, 7]
  assertHashSetEq r2 (Std.HashSet.ofList [3, 4])
  let r3 := similar_elements #[11, 12, 14, 13] #[17, 15, 14, 13]
  assertHashSetEq r3 (Std.HashSet.ofList [13, 14])
  return ()
