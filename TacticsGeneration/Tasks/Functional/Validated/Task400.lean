import Batteries

open Std

def extractFreq (test_list : List (Nat × Nat)) : Nat := Id.run do
  let canonicalize := fun (p : Nat × Nat) => if p.fst ≤ p.snd then p else (p.snd, p.fst)
  let mut s : HashSet (Nat × Nat) := HashSet.empty
  for p in test_list do
    s := s.insert (canonicalize p)
  return s.size

#guard extractFreq [(3, 4), (1, 2), (4, 3), (5, 6)] = 3
#guard extractFreq [(4, 15), (2, 3), (5, 4), (6, 7)] = 4
#guard extractFreq [(5, 16), (2, 3), (6, 5), (6, 9)] = 4
