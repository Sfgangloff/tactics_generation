import Batteries
open Std

def findVal? (m : Std.HashMap Nat Nat) (k : Nat) : Option Nat := Id.run do
  let mut r : Option Nat := none
  for (k', v) in m do
    if k' == k then
      r := some v
  return r

def freqCount (list1 : List Nat) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := Std.HashMap.emptyWithCapacity list1.length
  for x in list1 do
    let c := match findVal? m x with
      | some v => v
      | none => 0
    m := m.insert x (c + 1)
  return m

def mapEqPairs (m : Std.HashMap Nat Nat) (ps : List (Nat × Nat)) : Bool :=
  let sizeOk := m.size == ps.length
  let allOk := ps.foldl (fun acc (p : Nat × Nat) =>
    acc && (match findVal? m p.fst with
      | some v => v == p.snd
      | none => false)) true
  sizeOk && allOk

#guard mapEqPairs (freqCount [10,10,10,10,20,20,20,20,40,40,50,50,30]) [(10,4), (20,4), (40,2), (50,2), (30,1)]
#guard mapEqPairs (freqCount [1,2,3,4,3,2,4,1,3,1,4]) [(1,3), (2,2), (3,3), (4,3)]
#guard mapEqPairs (freqCount [5,6,7,4,9,10,4,5,6,7,9,5]) [(10,1), (5,3), (6,2), (7,2), (4,2), (9,2)]
