import Batteries

open Std

structure Node where
  value : Nat
  listNum : Nat
  index : Nat
  deriving Repr, BEq

def minNode (pq : List Node) : Option Node :=
  match pq with
  | [] => none
  | x :: xs => some <| xs.foldl (fun acc y => if y.value < acc.value then y else acc) x

def removeOne [BEq α] (xs : List α) (x : α) : List α :=
  match xs with
  | [] => []
  | z :: zs => if z == x then zs else z :: removeOne zs x

def extractMin (pq : List Node) : Option (Node × List Node) := do
  let some m := minNode pq | none
  let rest := removeOne pq m
  some (m, rest)

def findMinimumRange (lists : List (List Nat)) : Nat × Nat := Id.run do
  let mut pq : List Node := []
  let mut high : Nat := 0
  let mut first := true
  for i in [0 : lists.length] do
    let firstVal := (lists.getD i []).getD 0 0
    pq := { value := firstVal, listNum := i, index := 0 } :: pq
    if first then
      high := firstVal
      first := false
    else
      if firstVal > high then high := firstVal
  let mut pLow : Nat := 0
  let mut pHigh : Nat := 0
  let mut hasP := false
  let loopsBound := lists.foldl (fun acc sub => acc + sub.length) 0
  for _ in [: loopsBound + 1] do
    match extractMin pq with
    | none => break
    | some (top, rest) =>
      let low := top.value
      let i := top.listNum
      let j := top.index
      if !hasP || high - low < pHigh - pLow then
        pLow := low
        pHigh := high
        hasP := true
      let sub := lists.getD i []
      if j == sub.length - 1 then
        return (pLow, pHigh)
      let nextVal := sub.getD (j+1) 0
      pq := { value := nextVal, listNum := i, index := j+1 } :: rest
      if nextVal > high then high := nextVal
  return (pLow, pHigh)

#guard findMinimumRange [[3, 6, 8, 10, 15], [1, 5, 12], [4, 8, 15, 16], [2, 6]] = (4, 6)
#guard findMinimumRange [[2, 3, 4, 8, 10, 15], [1, 5, 12], [7, 8, 15, 16], [3, 6]] = (4, 7)
#guard findMinimumRange [[4, 7, 9, 11, 16], [2, 6, 13], [5, 9, 16, 17], [3, 7]] = (5, 7)
