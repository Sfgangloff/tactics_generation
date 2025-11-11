import Batteries
open Std

def insertSortedNat (x : Nat) : List Nat → List Nat
| [] => [x]
| y :: ys => if x ≤ y then x :: (y :: ys) else y :: insertSortedNat x ys

def sortNat : List Nat → List Nat
| [] => []
| x :: xs => insertSortedNat x (sortNat xs)

def mkMap (l : List (String × List Nat)) : HashMap String (List Nat) := Id.run do
  let mut m : HashMap String (List Nat) := HashMap.emptyWithCapacity 0
  for (k,v) in l do
    m := m.insert k v
  return m

def sortedDict (dict1 : HashMap String (List Nat)) : HashMap String (List Nat) := Id.run do
  let mut m : HashMap String (List Nat) := HashMap.emptyWithCapacity 0
  for (k, v) in dict1.toList do
    m := m.insert k (sortNat v)
  return m

def find? [BEq α] [Hashable α] (m : HashMap α β) (a : α) : Option β :=
  let rec go : List (α × β) → Option β
  | [] => none
  | (k, v) :: t => if k == a then some v else go t
  go m.toList

#guard (
  let input := Task662.mkMap [("n1", [2, 3, 1]), ("n2", [5, 1, 2]), ("n3", [3, 2, 4])]
  let res := Task662.sortedDict input
  ((res.find? "n1").getD [] == [1, 2, 3]) &&
  ((res.find? "n2").getD [] == [1, 2, 5]) &&
  ((res.find? "n3").getD [] == [2, 3, 4]) &&
  (res.size == 3)
)

#guard (
  let input := Task662.mkMap [("n1", [25, 37, 41]), ("n2", [41, 54, 63]), ("n3", [29, 38, 93])]
  let res := Task662.sortedDict input
  ((res.find? "n1").getD [] == [25, 37, 41]) &&
  ((res.find? "n2").getD [] == [41, 54, 63]) &&
  ((res.find? "n3").getD [] == [29, 38, 93]) &&
  (res.size == 3)
)

#guard (
  let input := Task662.mkMap [("n1", [58, 44, 56]), ("n2", [91, 34, 58]), ("n3", [100, 200, 300])]
  let res := Task662.sortedDict input
  ((res.find? "n1").getD [] == [44, 56, 58]) &&
  ((res.find? "n2").getD [] == [34, 58, 91]) &&
  ((res.find? "n3").getD [] == [100, 200, 300]) &&
  (res.size == 3)
)
