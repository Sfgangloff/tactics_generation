import Batteries

open Std

def removeFirst {α} [BEq α] (xs : List α) (y : α) : List α :=
  match xs with
  | [] => []
  | x :: xs' => if x == y then xs' else x :: removeFirst xs' y

def compareList {α} [Ord α] : List α → List α → Ordering
| [], [] => .eq
| [], _  => .lt
| _,  [] => .gt
| x :: xs, y :: ys =>
  match compare x y with
  | .lt => .lt
  | .gt => .gt
  | .eq => compareList xs ys

def selectionSortStableBy {α} [BEq α] (le : α → α → Bool) (xs : List α) : List α := Id.run do
  let lt (a b : α) := le a b && !(le b a)
  let n := xs.length
  let mut src := xs
  let mut res : List α := []
  for _ in [: n] do
    match src with
    | [] => ()
    | x :: xs' =>
      let minVal := (x :: xs').foldl (fun m a => if lt a m then a else m) x
      let rest := removeFirst (x :: xs') minVal
      res := res ++ [minVal]
      src := rest
  return res

def sortSublists {α} [Ord α] [BEq α] (list1 : List (List α)) : List (List α) :=
  let leLex (a b : List α) : Bool :=
    match compareList a b with
    | .gt => false
    | _   => true
  let byLex := selectionSortStableBy leLex list1
  let leLen (a b : List α) : Bool := Nat.ble a.length b.length
  selectionSortStableBy leLen byLex

#guard sortSublists [[2], [0], [1, 3], [0, 7], [9, 11], [13, 15, 17]] = [[0], [2], [0, 7], [1, 3], [9, 11], [13, 15, 17]]
#guard sortSublists [[1], [2, 3], [4, 5, 6], [7], [10, 11]] = [[1], [7], [2, 3], [10, 11], [4, 5, 6]]
#guard sortSublists [["python"], ["java", "C", "C++"], ["DBMS"], ["SQL", "HTML"]] = [["DBMS"], ["python"], ["SQL", "HTML"], ["java", "C", "C++"]]
