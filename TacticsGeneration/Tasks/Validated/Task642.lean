import Batteries

open Std

abbrev Pair := Nat × Nat

def lePair (p q : Pair) : Bool :=
  if Nat.blt p.fst q.fst then true
  else if Nat.blt q.fst p.fst then false
  else Nat.ble p.snd q.snd

def minByPair (xs : List Pair) : Option Pair :=
  match xs with
  | [] => none
  | h :: t => some <| t.foldl (fun acc x => if lePair x acc then x else acc) h

def removeOnePair (xs : List Pair) (x : Pair) : List Pair :=
  match xs with
  | [] => []
  | y :: ys => if y == x then ys else y :: removeOnePair ys x

def sortPairsDet (xs : List Pair) : List Pair := Id.run do
  let mut ys := xs
  let mut res : List Pair := []
  let n := ys.length
  for _ in [: n] do
    match minByPair ys with
    | none => ()
    | some m =>
      res := res ++ [m]
      ys := removeOnePair ys m
  return res

def removeSimilarRow (testList : List (List Pair)) : HashSet (List Pair) :=
  let processed := testList.map (fun sub =>
    let dedup := (HashSet.ofList sub).toList
    sortPairsDet dedup
  )
  HashSet.ofList processed

#guard removeSimilarRow [[(4, 5), (3, 2)], [(2, 2), (4, 6)], [(3, 2), (4, 5)]] ==
  HashSet.ofList [[(2, 2), (4, 6)], [(3, 2), (4, 5)]]
#guard removeSimilarRow [[(5, 6), (4, 3)], [(3, 3), (5, 7)], [(4, 3), (5, 6)]] ==
  HashSet.ofList [[(4, 3), (5, 6)], [(3, 3), (5, 7)]]
#guard removeSimilarRow [[(6, 7), (5, 4)], [(4, 4), (6, 8)], [(5, 4), (6, 7)]] ==
  HashSet.ofList [[(4, 4), (6, 8)], [(5, 4), (6, 7)]]
