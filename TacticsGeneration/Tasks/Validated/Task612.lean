import Batteries

open Std

def collectHeadsTails {α : Type} : List (List α) → Option (List α × List (List α))
| [] => some ([], [])
| (l :: rest) =>
  match l with
  | [] => none
  | h :: t =>
    match collectHeadsTails rest with
    | some (hs, ts) => some (h :: hs, t :: ts)
    | none => none

partial def transposeTrunc {α : Type} (xss : List (List α)) : List (List α) :=
  match collectHeadsTails xss with
  | some (hs, ts) => hs :: transposeTrunc ts
  | none => []

def merge {α : Type} (lst : List (List α)) : List (List α) :=
  transposeTrunc lst

#guard merge [["x", "y"], ["a", "b"], ["m", "n"]] == [["x", "a", "m"], ["y", "b", "n"]]
#guard merge [[1, 2], [3, 4], [5, 6], [7, 8]] == [[1, 3, 5, 7], [2, 4, 6, 8]]
#guard merge [["x", "y", "z"], ["a", "b", "c"], ["m", "n", "o"]] == [["x", "a", "m"], ["y", "b", "n"], ["z", "c", "o"]]
