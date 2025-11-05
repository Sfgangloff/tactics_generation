import Batteries

open Std

class Cmp (α : Type) where
  lt : α → α → Bool

def natLt (a b : Nat) : Bool :=
  Nat.ble (a + 1) b

def charLt (a b : Char) : Bool :=
  natLt a.toNat b.toNat

instance : Cmp Nat where
  lt := fun a b => natLt a b

instance : Cmp String where
  lt := fun a b =>
    let rec go (xs ys : List Char) : Bool :=
      match xs, ys with
      | [], [] => false
      | [], _ => true
      | _, [] => false
      | x::xs, y::ys => if x == y then go xs ys else charLt x y
    go a.data b.data

instance : Cmp (List Nat) where
  lt := fun xs ys =>
    let rec go (xs ys : List Nat) : Bool :=
      match xs, ys with
      | [], [] => false
      | [], _ => true
      | _, [] => false
      | x::xs, y::ys => if Nat.beq x y then go xs ys else natLt x y
    go xs ys

def insertBy {α} (lt : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if lt x y then x :: y :: ys else y :: insertBy lt x ys

def isort {α} (lt : α → α → Bool) (xs : List α) : List α :=
  xs.foldl (fun acc x => insertBy lt x acc) []

def dedupAdj {α} [BEq α] (xs : List α) : List α :=
  let rec go (prev? : Option α) (acc : List α) (ys : List α) : List α :=
    match ys with
    | [] => acc.reverse
    | y :: ys' =>
      match prev? with
      | some p =>
        if y == p then go prev? acc ys' else go (some y) (y :: acc) ys'
      | none => go (some y) (y :: acc) ys'
  go none [] xs

def remove_duplicate {α} [Cmp α] [BEq α] (list1 : List α) : List α :=
  let sorted := isort (Cmp.lt) list1
  dedupAdj sorted

#guard remove_duplicate [[10, 20], [40], [30, 56, 25], [10, 20], [33], [40]] = [[10, 20], [30, 56, 25], [33], [40]]
#guard remove_duplicate ["a", "b", "a", "c", "c"] = ["a", "b", "c"]
#guard remove_duplicate [1, 3, 5, 6, 3, 5, 6, 1] = [1, 3, 5, 6]
