import Batteries
open Std

def lookupHMNat (m : Std.HashMap Nat Nat) (k : Nat) : Option Nat := Id.run do
  let mut res : Option Nat := none
  for (k2, v2) in m do
    if k2 = k then
      res := some v2
  return res

def freqElement (nums : List (List Nat)) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  for sub in nums do
    for x in sub do
      let c := (lookupHMNat m x).getD 0
      m := m.insert x (c + 1)
  return m

def hashMapEqNat (m1 m2 : Std.HashMap Nat Nat) : Bool := Id.run do
  if m1.size != m2.size then
    return false
  let mut ok := true
  for (k, v) in m1 do
    match lookupHMNat m2 k with
    | some v2 => if v2 != v then ok := false
    | none => ok := false
    if !ok then break
  return ok

#guard hashMapEqNat (freqElement [[1, 2, 3, 2], [4, 5, 6, 2], [7, 1, 9, 5]]) (Std.HashMap.ofList [(2, 3), (1, 2), (5, 2), (3, 1), (4, 1), (6, 1), (7, 1), (9, 1)])
#guard hashMapEqNat (freqElement [[1,2,3,4],[5,6,7,8],[9,10,11,12]]) (Std.HashMap.ofList [(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1),(8,1),(9,1),(10,1),(11,1),(12,1)])
#guard hashMapEqNat (freqElement [[15,20,30,40],[80,90,100,110],[30,30,80,90]]) (Std.HashMap.ofList [(30,3),(80,2),(90,2),(15,1),(20,1),(40,1),(100,1),(110,1)])
