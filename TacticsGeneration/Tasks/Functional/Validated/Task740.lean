import Batteries
open Std

def tupleToDict (testTup : List Nat) : HashMap Nat Nat :=
  let rec loop (l : List Nat) (m : HashMap Nat Nat) : HashMap Nat Nat :=
    match l with
    | k :: v :: rest => loop rest (m.insert k v)
    | _ => m
  loop testTup ({} : HashMap Nat Nat)

def lookupNat (m : HashMap Nat Nat) (k : Nat) : Option Nat :=
  let rec go (l : List (Nat × Nat)) : Option Nat :=
    match l with
    | [] => none
    | (k', v) :: t => if k' == k then some v else go t
  go m.toList

def mapEqNat (m1 m2 : HashMap Nat Nat) : Bool :=
  if m1.size != m2.size then false
  else
    let b1 := m1.toList.all (fun (kv : Nat × Nat) =>
      match lookupNat m2 kv.fst with
      | some v2 => v2 == kv.snd
      | none => false)
    let b2 := m2.toList.all (fun (kv : Nat × Nat) =>
      match lookupNat m1 kv.fst with
      | some v1 => v1 == kv.snd
      | none => false)
    b1 && b2

#guard mapEqNat (tupleToDict [1, 5, 7, 10, 13, 5]) (HashMap.ofList [(1, 5), (7, 10), (13, 5)]) == true
#guard mapEqNat (tupleToDict [1, 2, 3, 4, 5, 6]) (HashMap.ofList [(1, 2), (3, 4), (5, 6)]) == true
#guard mapEqNat (tupleToDict [7, 8, 9, 10, 11, 12]) (HashMap.ofList [(7, 8), (9, 10), (11, 12)]) == true
