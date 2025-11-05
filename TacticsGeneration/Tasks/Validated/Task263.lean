import Batteries
open Std

def hashMapOfList (l : List (String × Nat)) : HashMap String Nat :=
  HashMap.ofList l

def mapsEqual (m1 m2 : HashMap String Nat) : Bool :=
  let rec check (ps : List (String × Nat)) : Bool :=
    match ps with
    | [] => true
    | (k, v) :: ps =>
      let rec find (l : List (String × Nat)) : Option Nat :=
        match l with
        | [] => none
        | (k', v') :: t =>
          if k == k' then some v' else find t
      match find (m2.toList) with
      | some v2 => if v == v2 then check ps else false
      | none => false
  check m1.toList && check m2.toList

def mergeDict (d1 d2 : HashMap String Nat) : HashMap String Nat := Id.run do
  let mut d := d1
  for (k, v) in d2.toList do
    d := d.insert k v
  return d

#guard mapsEqual (mergeDict (hashMapOfList [("a", 100), ("b", 200)]) (hashMapOfList [("x", 300), ("y", 200)])) (hashMapOfList [("x", 300), ("y", 200), ("a", 100), ("b", 200)])
#guard mapsEqual (mergeDict (hashMapOfList [("a",900),("b",900),("d",900)]) (hashMapOfList [("a",900),("b",900),("d",900)])) (hashMapOfList [("a",900),("b",900),("d",900),("a",900),("b",900),("d",900)])
#guard mapsEqual (mergeDict (hashMapOfList [("a",10),("b",20)]) (hashMapOfList [("x",30),("y",40)])) (hashMapOfList [("x",30),("y",40),("a",10),("b",20)])
