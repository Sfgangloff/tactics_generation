import Batteries

open Std

structure Model where
  make : String
  model : Nat
  color : String
  deriving Repr, BEq, DecidableEq

def insertBy {α β} [Ord β] (key : α → β) (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
    match compare (key x) (key y) with
    | Ordering.lt => x :: y :: ys
    | _ => y :: insertBy key x ys

def insertionSortBy {α β} [Ord β] (key : α → β) (xs : List α) : List α :=
  xs.foldl (fun acc x => insertBy key x acc) []

def sortedModels (models : List Model) : List Model :=
  insertionSortBy (fun m => m.color) models

#guard sortedModels [
  { make := "Nokia", model := 216, color := "Black" },
  { make := "Mi Max", model := 2, color := "Gold" },
  { make := "Samsung", model := 7, color := "Blue" }
] = [
  { make := "Nokia", model := 216, color := "Black" },
  { make := "Samsung", model := 7, color := "Blue" },
  { make := "Mi Max", model := 2, color := "Gold" }
]

#guard sortedModels [
  { make := "Vivo", model := 20, color := "Blue" },
  { make := "oppo", model := 17, color := "Gold" },
  { make := "Apple", model := 11, color := "red" }
] = [
  { make := "Vivo", model := 20, color := "Blue" },
  { make := "oppo", model := 17, color := "Gold" },
  { make := "Apple", model := 11, color := "red" }
]

#guard sortedModels [
  { make := "micromax", model := 40, color := "grey" },
  { make := "poco", model := 60, color := "blue" }
] = [
  { make := "poco", model := 60, color := "blue" },
  { make := "micromax", model := 40, color := "grey" }
]
