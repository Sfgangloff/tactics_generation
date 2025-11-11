import Batteries
open Std

@[inline] def find? {α β} [BEq α] [Hashable α] (m : HashMap α β) (a : α) : Option β :=
  m.get? a

def beqHashMap [BEq α] [Hashable α] [BEq β] (m n : HashMap α β) : Bool := Id.run do
  if m.size != n.size then
    return false
  let mut ok := true
  for (k, v) in m.toList do
    if ok then
      match n.find? k with
      | some v2 =>
        if v == v2 then
          pure ()
        else
          ok := false
      | none =>
        ok := false
    else
      pure ()
  return ok

instance instBEqHashMap [BEq α] [Hashable α] [BEq β] : BEq (HashMap α β) where
  beq m n := beqHashMap m n

def check_occurences (test_list : List (Nat × Nat)) : HashMap (Nat × Nat) Nat := Id.run do
  let mut m : HashMap (Nat × Nat) Nat := {}
  for (a, b) in test_list do
    let p := if a ≤ b then (a, b) else (b, a)
    let c := match m.find? p with
      | some n => n + 1
      | none => 1
    m := m.insert p c
  return m

#guard check_occurences [(3, 1), (1, 3), (2, 5), (5, 2), (6, 3)] == HashMap.ofList [((1, 3), 2), ((2, 5), 2), ((3, 6), 1)]
#guard check_occurences [(4, 2), (2, 4), (3, 6), (6, 3), (7, 4)] == HashMap.ofList [((2, 4), 2), ((3, 6), 2), ((4, 7), 1)]
#guard check_occurences [(13, 2), (11, 23), (12, 25), (25, 12), (16, 23)] == HashMap.ofList [((2, 13), 1), ((11, 23), 1), ((12, 25), 2), ((16, 23), 1)]
