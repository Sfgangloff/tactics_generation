import Batteries
open Std

def listMin (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: xs => xs.foldl (fun m y => if y < m then y else m) x

def removeOne (xs : List Nat) (x : Nat) : List Nat :=
  match xs with
  | [] => []
  | y :: ys => if y == x then ys else y :: removeOne ys x

def getAtD {α} (xs : List α) (i : Nat) (dflt : α) : α :=
  match xs.drop i with
  | [] => dflt
  | y :: _ => y

def selectionSortNat (xs : List Nat) : List Nat :=
  let rec go (ys : List Nat) (acc : List Nat) (fuel : Nat) : List Nat :=
    match fuel with
    | 0 => acc ++ ys
    | fuel' + 1 =>
      match ys with
      | [] => acc
      | _ =>
        let m := listMin ys
        let ys' := removeOne ys m
        go ys' (acc ++ [m]) fuel'
  go xs [] xs.length

def findInd (key i n k : Nat) (arr : List Nat) : Int :=
  let start0 := i + 1
  let end0 := n - 1
  let rec loop (start_ end_ : Nat) (ind : Int) (fuel : Nat) : Int :=
    match fuel with
    | 0 => ind
    | fuel' + 1 =>
      if start_ < end_ then
        let mid := start_ + (end_ - start_) / 2
        let midVal := getAtD arr mid 0
        if midVal ≤ key + k then
          loop (mid + 1) end_ (Int.ofNat mid) fuel'
        else
          loop start_ mid ind fuel'
      else
        ind
  loop start0 end0 (-1) (n + 1)

def removals (arr : List Nat) (n k : Nat) : Nat := Id.run do
  let arrS := selectionSortNat arr
  let mut ans := n - 1
  for i in [0 : n] do
    let key := getAtD arrS i 0
    let j := findInd key i n k arrS
    if j != (-1) then
      let jNat := Int.toNat j
      let segLen := (jNat - i) + 1
      let cand := n - segLen
      ans := Nat.min ans cand
  return ans

#guard removals [1, 3, 4, 9, 10, 11, 12, 17, 20] 9 4 == 5
#guard removals [1, 5, 6, 2, 8] 5 2 == 3
#guard removals [1, 2, 3, 4, 5, 6] 6 3 == 2
