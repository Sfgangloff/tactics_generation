import Batteries

open Std

structure Node where
  s : Nat
  i : Nat
  j : Nat
  deriving Repr, BEq

def lexLess (x y : Node) : Bool :=
  if x.s < y.s then true
  else if x.s > y.s then false
  else if x.i < y.i then true
  else if x.i > y.i then false
  else x.j < y.j

def extractMin (q : List Node) : Option (Node × List Node) :=
  match q with
  | [] => none
  | x :: xs =>
    let (best, acc) := xs.foldl (fun (best, acc) y =>
      if lexLess y best then (y, best :: acc) else (best, y :: acc)) (x, ([] : List Node))
    some (best, acc.reverse)

def kSmallestPairs (nums1 nums2 : List Nat) (k : Nat) : List (List Nat) := Id.run do
  let push := fun (q : List Node) (i j : Nat) =>
    if i < nums1.length && j < nums2.length then
      let s := nums1.getD i 0 + nums2.getD j 0
      ({ s := s, i := i, j := j } :: q)
    else q
  let mut q : List Node := []
  q := push q 0 0
  let mut res : Array (List Nat) := #[]
  for _ in [:k] do
    match extractMin q with
    | none => break
    | some (node, q2) =>
      res := res.push [nums1.getD node.i 0, nums2.getD node.j 0]
      q := push q2 node.i (node.j + 1)
      if node.j == 0 then
        q := push q (node.i + 1) 0
  return res.toList

#guard kSmallestPairs [1,3,7] [2,4,6] 2 == [[1, 2], [1, 4]]
#guard kSmallestPairs [1,3,7] [2,4,6] 1 == [[1, 2]]
#guard kSmallestPairs [1,3,7] [2,4,6] 7 == [[1, 2], [1, 4], [3, 2], [1, 6], [3, 4], [3, 6], [7, 2]]
