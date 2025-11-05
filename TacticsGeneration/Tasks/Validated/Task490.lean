import Batteries

open Std

def ltBool (a b : Nat) : Bool :=
  Nat.ble (a + 1) b

def extractSymmetric (test_list : List (Nat × Nat)) : HashSet (Nat × Nat) := Id.run do
  let s1 : HashSet (Nat × Nat) := HashSet.ofList test_list
  let swappedList := test_list.map (fun p => (p.snd, p.fst))
  let s2 : HashSet (Nat × Nat) := HashSet.ofList swappedList
  let temp := s1.filter (fun x => x ∈ s2)
  let res := temp.filter (fun p => ltBool p.fst p.snd)
  return res

#guard extractSymmetric [(6, 7), (2, 3), (7, 6), (9, 8), (10, 2), (8, 9)] == HashSet.ofList [(8, 9), (6, 7)]
#guard extractSymmetric [(7, 8), (3, 4), (8, 7), (10, 9), (11, 3), (9, 10)] == HashSet.ofList [(9, 10), (7, 8)]
#guard extractSymmetric [(8, 9), (4, 5), (9, 8), (11, 10), (12, 4), (10, 11)] == HashSet.ofList [(8, 9), (10, 11)]
