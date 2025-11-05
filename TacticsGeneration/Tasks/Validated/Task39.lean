import Batteries

open Std

def countChar (xs : List Char) (c : Char) : Nat :=
  xs.foldl (fun acc x => if x == c then acc + 1 else acc) 0

def dedupChars (xs : List Char) : List Char :=
  let rec go (xs : List Char) (seen : HashSet Char) (acc : List Char) : List Char :=
    match xs with
    | [] => acc.reverse
    | c :: cs =>
      if seen.contains c then
        go cs seen acc
      else
        go cs (seen.insert c) (c :: acc)
  go xs ({} : HashSet Char) []

private def pairBetter (a b : Nat × Char) : Bool :=
  if a.fst == b.fst then a.snd < b.snd else a.fst > b.fst

def pickMax (xs : List (Nat × Char)) : Option ((Nat × Char) × List (Nat × Char)) :=
  match xs with
  | [] => none
  | x :: xs =>
    let rec go (best : Nat × Char) (ys : List (Nat × Char)) (acc : List (Nat × Char)) : (Nat × Char) × List (Nat × Char) :=
      match ys with
      | [] => (best, acc.reverse)
      | y :: ys' =>
        if pairBetter y best then
          go y ys' (best :: acc)
        else
          go best ys' (y :: acc)
    let (best, rest) := go x xs []
    some (best, rest)

partial def loopRearr (pairs : List (Nat × Char)) (remaining : Nat) (ans : String) : String :=
  if remaining == 0 then
    ans
  else
    match pickMax pairs with
    | none => ans
    | some (p1, rest1) =>
      if remaining == 1 then
        ans.push p1.snd
      else
        match pickMax rest1 with
        | none => ans.push p1.snd
        | some (p2, rest2) =>
          let ans' := (ans.push p1.snd).push p2.snd
          let rest2' :=
            let l0 := rest2
            let l1 := if p1.fst - 1 > 0 then (p1.fst - 1, p1.snd) :: l0 else l0
            let l2 := if p2.fst - 1 > 0 then (p2.fst - 1, p2.snd) :: l1 else l1
            l2
          loopRearr rest2' (remaining - 2) ans'

def rearangeString (S : String) : String :=
  let chars := S.toList
  let uniq := dedupChars chars
  let pairs : List (Nat × Char) := uniq.map (fun c => (countChar chars c, c))
  let maxCount := pairs.foldl (fun m p => Nat.max m p.fst) 0
  let n := S.length
  if maxCount * 2 > n + 1 then
    ""
  else
    loopRearr pairs n ""

#guard rearangeString "aab" == "aba"
#guard rearangeString "aabb" == "abab"
#guard rearangeString "abccdd" == "cdabcd"
