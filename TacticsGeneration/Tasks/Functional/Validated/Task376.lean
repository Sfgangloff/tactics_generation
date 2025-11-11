import Batteries

open Std

def removeReplica (test_tup : List Nat) : List (Sum Nat String) := Id.run do
  let mut seen : HashSet Nat := {}
  let mut res : Array (Sum Nat String) := #[]
  for ele in test_tup do
    if seen.contains ele then
      res := res.push (Sum.inr "MSP")
    else
      seen := seen.insert ele
      res := res.push (Sum.inl ele)
  return res.toList

#guard removeReplica [1, 1, 4, 4, 4, 5, 5, 6, 7, 7] == [Sum.inl 1, Sum.inr "MSP", Sum.inl 4, Sum.inr "MSP", Sum.inr "MSP", Sum.inl 5, Sum.inr "MSP", Sum.inl 6, Sum.inl 7, Sum.inr "MSP"]
#guard removeReplica [2, 3, 4, 4, 5, 6, 6, 7, 8, 9, 9] == [Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inr "MSP", Sum.inl 5, Sum.inl 6, Sum.inr "MSP", Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inr "MSP"]
#guard removeReplica [2, 2, 5, 4, 5, 7, 5, 6, 7, 7] == [Sum.inl 2, Sum.inr "MSP", Sum.inl 5, Sum.inl 4, Sum.inr "MSP", Sum.inl 7, Sum.inr "MSP", Sum.inl 6, Sum.inr "MSP", Sum.inr "MSP"]
