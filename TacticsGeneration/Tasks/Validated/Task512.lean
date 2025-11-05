import Batteries
open Std

inductive NestedTuple where
| int : Nat → NestedTuple
| tuple : List NestedTuple → NestedTuple
deriving Repr

def flatten (t : NestedTuple) : List Nat :=
  match t with
  | .int n => [n]
  | .tuple xs => xs.flatMap flatten

def count_element_freq (test_tuple : NestedTuple) : Std.HashMap Nat Nat := Id.run do
  let mut res : Std.HashMap Nat Nat := {}
  for ele in flatten test_tuple do
    let c := (res.get? ele).getD 0
    res := res.insert ele (c + 1)
  return res

def mapOfList (xs : List (Nat × Nat)) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  for (k, v) in xs do
    m := m.insert k v
  return m

def mapsEqual (m1 m2 : Std.HashMap Nat Nat) : Bool := Id.run do
  if m1.size == m2.size then
    let mut ok := true
    for (k, v) in m1.toList do
      if ((m2.get? k).getD 0) == v then
        pure ()
      else
        ok := false
    return ok
  else
    return false

def t1 : Task512.NestedTuple :=
  .tuple [
    .int 5, .int 6, .tuple [.int 5, .int 6], .int 7, .tuple [.int 8, .int 9], .int 9
  ]
#guard mapsEqual (count_element_freq t1) (mapOfList [(5,2), (6,2), (7,1), (8,1), (9,2)])

def t2 : Task512.NestedTuple :=
  .tuple [
    .int 6, .int 7, .tuple [.int 6, .int 7], .int 8, .tuple [.int 9, .int 10], .int 10
  ]
#guard mapsEqual (count_element_freq t2) (mapOfList [(6,2), (7,2), (8,1), (9,1), (10,2)])

def t3 : Task512.NestedTuple :=
  .tuple [
    .int 7, .int 8, .tuple [.int 7, .int 8], .int 9, .tuple [.int 10, .int 11], .int 11
  ]
#guard mapsEqual (count_element_freq t3) (mapOfList [(7,2), (8,2), (9,1), (10,1), (11,2)])
