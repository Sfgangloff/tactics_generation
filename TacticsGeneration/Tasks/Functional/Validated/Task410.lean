import Batteries

open Std

def onlyInts (l : List (Sum String Nat)) : List Nat :=
  l.foldr (fun x acc => match x with
    | Sum.inr n => n :: acc
    | Sum.inl _ => acc) []

def listMin (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | y :: ys => ys.foldl (fun m n => if n < m then n else m) y

def min_val (listval : List (Sum String Nat)) : Nat :=
  listMin (onlyInts listval)

#guard min_val [Sum.inl "Python", Sum.inr 3, Sum.inr 2, Sum.inr 4, Sum.inr 5, Sum.inl "version"] = 2
#guard min_val [Sum.inl "Python", Sum.inr 15, Sum.inr 20, Sum.inr 25] = 15
#guard min_val [Sum.inl "Python", Sum.inr 30, Sum.inr 20, Sum.inr 40, Sum.inr 50, Sum.inl "version"] = 20
