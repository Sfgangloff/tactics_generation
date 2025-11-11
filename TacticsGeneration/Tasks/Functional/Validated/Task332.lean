import Batteries
open Std

def charFrequency (str1 : String) : Std.HashMap Char Nat := Id.run do
  let mut dict : Std.HashMap Char Nat := Std.HashMap.emptyWithCapacity str1.length
  for c in str1.data do
    let old := (dict[c]?).getD 0
    dict := dict.insert c (old + 1)
  return dict

def entriesCharNat (m : Std.HashMap Char Nat) : List (Char × Nat) :=
  m.fold (init := []) (fun acc k v => (k, v) :: acc)

def hashMapOfList (xs : List (Char × Nat)) : Std.HashMap Char Nat := Id.run do
  let mut m : Std.HashMap Char Nat := Std.HashMap.emptyWithCapacity xs.length
  for (k, v) in xs do
    m := m.insert k v
  return m

def hashMapEq (m1 m2 : Std.HashMap Char Nat) : Bool := Id.run do
  if m1.size != m2.size then return false
  for (k, v) in entriesCharNat m2 do
    match m1[k]? with
    | some v' => if v' != v then return false
    | none => return false
  return true

#guard hashMapEq (charFrequency "python") (hashMapOfList [('p', 1), ('y', 1), ('t', 1), ('h', 1), ('o', 1), ('n', 1)])
#guard hashMapEq (charFrequency "program") (hashMapOfList [('p', 1), ('r', 2), ('o', 1), ('g', 1), ('a', 1), ('m', 1)])
#guard hashMapEq (charFrequency "language") (hashMapOfList [('l', 1), ('a', 2), ('n', 1), ('g', 2), ('u', 1), ('e', 1)])
