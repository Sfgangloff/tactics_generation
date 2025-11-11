import Batteries
open Std

def frequencyLists (list1 : List (List Nat)) : Std.HashMap Nat Nat := Id.run do
  let flat : List Nat := List.join list1
  let mut m : Std.HashMap Nat Nat := Std.HashMap.empty
  for num in flat do
    let prev : Nat := (m.find? num).getD 0
    m := m.insert num (prev + 1)
  return m

instance : BEq (Std.HashMap Nat Nat) where
  beq a b :=
    if a.size == b.size then
      (a.toList).all (fun (k, v) =>
        match (b.toList).find? (fun p => p.fst == k) with
        | some p2 => p2.snd == v
        | none => false)
    else
      false

#guard frequencyLists [[1, 2, 3, 2], [4, 5, 6, 2], [7, 8, 9, 5]] == Std.HashMap.ofList [(1, 1), (2, 3), (3, 1), (4, 1), (5, 2), (6, 1), (7, 1), (8, 1), (9, 1)]
#guard frequencyLists [[1,2,3,4],[5,6,7,8],[9,10,11,12]] == Std.HashMap.ofList [(1,1), (2,1), (3,1), (4,1), (5,1), (6,1), (7,1), (8,1), (9,1), (10,1), (11,1), (12,1)]
#guard frequencyLists [[20,30,40,17],[18,16,14,13],[10,20,30,40]] == Std.HashMap.ofList [(20,2), (30,2), (40,2), (17,1), (18,1), (16,1), (14,1), (13,1), (10,1)]
