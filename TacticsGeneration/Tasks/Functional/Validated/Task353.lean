import Batteries

open Std

def removeAtIdx {α} (xs : List α) (n : Nat) : List α :=
  let rec go (ys : List α) (k : Nat) : (List α × Bool) :=
    match ys, k with
    | [], _ => ([], false)
    | _::ys, 0 => (ys, true)
    | y::ys, k+1 =>
      let (rest, done) := go ys k
      if done then (y :: rest, true) else (y :: rest, false)
  let (res, done) := go xs n
  if done then res else xs

def removeColumn (list1 : List (List Int)) (n : Nat) : List (List Int) :=
  list1.map (fun row => removeAtIdx row n)

#guard removeColumn [[1, 2, 3], [2, 4, 5], [1, 1, 1]] 0 = [[2, 3], [4, 5], [1, 1]]
#guard removeColumn [[1, 2, 3], [-2, 4, -5], [1, -1, 1]] 2 = [[1, 2], [-2, 4], [1, -1]]
#guard removeColumn [[1, 3], [5, 7], [1, 3], [13, 15, 17], [5, 7], [9, 11]] 0 = [[3], [7], [3], [15, 17], [7], [11]]
