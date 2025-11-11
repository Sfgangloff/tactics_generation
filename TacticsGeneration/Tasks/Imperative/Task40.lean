import Batteries
open Std

namespace Task40

/--
  freqElement flattens a nested array of Nats and counts element frequencies.
  Preconditions: indices assumed valid when accessing arrays.
-/
def freqElement (nums : Array (Array Nat)) : Std.HashMap Nat Nat := Id.run do
  let mut hm : Std.HashMap Nat Nat := Std.HashMap.empty
  for sub in nums do
    for x in sub do
      let prev :=
        match Std.HashMap.find? hm x with
        | some v => v
        | none => 0
      hm := Std.HashMap.insert hm x (prev + 1)
  return hm

end Task40

instance [BEq α] [Hashable α] [BEq β] : BEq (Std.HashMap α β) where
  beq m1 m2 :=
    Id.run do
      if Std.HashMap.size m1 != Std.HashMap.size m2 then
        return false
      let mut ok := true
      let kvs := Std.HashMap.toList m1
      for (k, v) in kvs do
        match Std.HashMap.find? m2 k with
        | some v2 =>
          if v == v2 then
            ()
          else
            ok := false
        | none =>
          ok := false
      return ok

-- Tests

/-- helper to build a HashMap from key/value pairs -/
def buildMap (pairs : Array (Nat × Nat)) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := Std.HashMap.empty
  for (k, v) in pairs do
    m := Std.HashMap.insert m k v
  return m

-- Test 1
#eval
  let got := Task40.freqElement #[(#[(1),(2),(3),(2)]), (#[(4),(5),(6),(2)]), (#[(7),(1),(9),(5)])]
  let expected := buildMap #[(2,3),(1,2),(5,2),(3,1),(4,1),(6,1),(7,1),(9,1)]
  if got == expected then () else panic! "Test 1 failed"

-- Test 2
#eval
  let got := Task40.freqElement #[(#[(1),(2),(3),(4)]), (#[(5),(6),(7),(8)]), (#[(9),(10),(11),(12)])]
  let expected := buildMap #[(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1),(8,1),(9,1),(10,1),(11,1),(12,1)]
  if got == expected then () else panic! "Test 2 failed"

-- Test 3
#eval
  let got := Task40.freqElement #[(#[(15),(20),(30),(40)]), (#[(80),(90),(100),(110)]), (#[(30),(30),(80),(90)])]
  let expected := buildMap #[(30,3),(80,2),(90,2),(15,1),(20,1),(40,1),(100,1),(110,1)]
  if got == expected then () else panic! "Test 3 failed"