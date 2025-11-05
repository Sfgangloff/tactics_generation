import Batteries

open Std

def tupleIntersection (testList1 testList2 : List (Nat × Nat)) : HashSet (Nat × Nat) := Id.run do
  let norm (p : Nat × Nat) : Nat × Nat :=
    let a := p.fst
    let b := p.snd
    if a ≤ b then (a, b) else (b, a)
  let s1 := HashSet.ofList (testList1.map norm)
  let s2 := HashSet.ofList (testList2.map norm)
  return s1.filter (fun x => x ∈ s2)

#guard tupleIntersection [(3, 4), (5, 6), (9, 10), (4, 5)] [(5, 4), (3, 4), (6, 5), (9, 11)] == HashSet.ofList [(4, 5), (3, 4), (5, 6)]
#guard tupleIntersection [(4, 1), (7, 4), (11, 13), (17, 14)] [(1, 4), (7, 4), (16, 12), (10, 13)] == HashSet.ofList [(4, 7), (1, 4)]
#guard tupleIntersection [(2, 1), (3, 2), (1, 3), (1, 4)] [(11, 2), (2, 3), (6, 2), (1, 3)] == HashSet.ofList [(1, 3), (2, 3)]
