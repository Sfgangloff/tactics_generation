import Batteries

open Std

def containsNat (xs : List Nat) (x : Nat) : Bool :=
  xs.any (fun y => y == x)

def eraseDupsNat (xs : List Nat) : List Nat :=
  let rec go (ys : List Nat) (acc : List Nat) : List Nat :=
    match ys with
    | [] => acc.reverse
    | y :: ys' =>
      if containsNat acc y then go ys' acc else go ys' (y :: acc)
  go xs []

def insertKV (m : List (Nat × List Nat)) (k v : Nat) : List (Nat × List Nat) :=
  match m with
  | [] => [(k, [v])]
  | (k', vs) :: rest =>
    if k' == k then (k', vs ++ [v]) :: rest else (k', vs) :: insertKV rest k v

def dictToStringNatNat (pairs : List (Nat × Nat)) : String :=
  let (body, _) := pairs.foldl (fun (st : String × Bool) (kv : Nat × Nat) =>
    let (acc, first) := st
    let sep := if first then "" else ", "
    let piece := sep ++ toString kv.fst ++ ": " ++ toString kv.snd
    (acc ++ piece, false)
  ) ("", true)
  "{" ++ body ++ "}"

def getUnique (testList : List (Nat × Nat)) : String := Id.run do
  
  let mut res : List (Nat × List Nat) := []
  for sub in testList do
    let v := sub.fst
    let k := sub.snd
    res := insertKV res k v
  
  let counts : List (Nat × Nat) := res.map (fun (k, vs) => (k, (eraseDupsNat vs).length))
  return dictToStringNatNat counts

#guard getUnique [(3, 4), (1, 2), (2, 4), (8, 2), (7, 2), (8, 1), (9, 1), (8, 4), (10, 4)] == "{4: 4, 2: 3, 1: 2}"
#guard getUnique [(4, 5), (2, 3), (3, 5), (9, 3), (8, 3), (9, 2), (10, 2), (9, 5), (11, 5)] == "{5: 4, 3: 3, 2: 2}"
#guard getUnique [(6, 5), (3, 4), (2, 6), (11, 1), (8, 22), (8, 11), (4, 3), (14, 3), (11, 6)] == "{5: 1, 4: 1, 6: 2, 1: 1, 22: 1, 11: 1, 3: 2}"
