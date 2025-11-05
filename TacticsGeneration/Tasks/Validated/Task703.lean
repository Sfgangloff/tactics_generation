import Batteries
open Std

def isKeyPresent (d : Std.HashMap Nat Nat) (x : Nat) : Bool :=
  d.contains x

def mkMap (xs : List (Nat × Nat)) : Std.HashMap Nat Nat :=
  xs.foldl (fun (m : Std.HashMap Nat Nat) (k, v) => m.insert k v) (Std.HashMap.emptyWithCapacity (α := Nat) (β := Nat) xs.length)

#guard isKeyPresent (mkMap [(1,10), (2,20), (3,30), (4,40), (5,50), (6,60)]) 5 == true
#guard isKeyPresent (mkMap [(1,10), (2,20), (3,30), (4,40), (5,50), (6,60)]) 6 == true
#guard isKeyPresent (mkMap [(1,10), (2,20), (3,30), (4,40), (5,50), (6,60)]) 10 == false
