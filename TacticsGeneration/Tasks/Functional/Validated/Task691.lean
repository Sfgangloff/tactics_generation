import Batteries
open Std

def insertBy {α} (lt : α → α → Bool) (x : α) : List α → List α
| [] => [x]
| y :: ys => if lt y x then y :: insertBy lt x ys else x :: y :: ys

def isort {α} (lt : α → α → Bool) : List α → List α
| [] => []
| x :: xs => insertBy lt x (isort lt xs)

def findVal? [BEq α] [Hashable α] (m : Std.HashMap α β) (k : α) : Option β :=
  let rec go : List (α × β) → Option β
  | [] => none
  | (k', v) :: xs => if k' == k then some v else go xs
  go m.toList

def groupElement (test_list : List (Nat × Nat)) : Std.HashMap Nat (List Nat) :=
  let sorted := isort (fun a b => Nat.blt a.snd b.snd) test_list
  let rec go (l : List (Nat × Nat)) (res : Std.HashMap Nat (List Nat)) : Std.HashMap Nat (List Nat) :=
    match l with
    | [] => res
    | (a, b) :: xs =>
      let old := (findVal? res b).getD []
      let res' := res.insert b (old ++ [a])
      go xs res'
  go sorted {}

def mapEqList (m : Std.HashMap Nat (List Nat)) (l : List (Nat × List Nat)) : Bool :=
  let okVals := l.all (fun kv =>
    let k := kv.fst
    let v := kv.snd
    match findVal? m k with
    | some v' => v' == v
    | none => false)
  okVals && (m.size == l.length)

#guard mapEqList (groupElement [(6, 5), (2, 7), (2, 5), (8, 7), (9, 8), (3, 7)]) [(5, [6, 2]), (7, [2, 8, 3]), (8, [9])] = true
#guard mapEqList (groupElement [(7, 6), (3, 8), (3, 6), (9, 8), (10, 9), (4, 8)]) [(6, [7, 3]), (8, [3, 9, 4]), (9, [10])] = true
#guard mapEqList (groupElement [(8, 7), (4, 9), (4, 7), (10, 9), (11, 10), (5, 9)]) [(7, [8, 4]), (9, [4, 10, 5]), (10, [11])] = true
