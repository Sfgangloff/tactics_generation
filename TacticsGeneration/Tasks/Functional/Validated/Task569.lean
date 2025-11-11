import Batteries

open Std

def insertBy {α} (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: insertBy le x ys

def isort {α} (le : α → α → Bool) (xs : List α) : List α :=
  xs.foldr (fun x acc => insertBy le x acc) []

def strLe (a b : String) : Bool :=
  match compare a b with
  | Ordering.lt => true
  | Ordering.eq => true
  | Ordering.gt => false

def sortSublists (list1 : List (List String)) : List (List String) :=
  list1.map (fun xs => isort strLe xs)

#guard sortSublists [["green", "orange"], ["black", "white"], ["white", "black", "orange"]] == [["green", "orange"], ["black", "white"], ["black", "orange", "white"]]
#guard sortSublists [["green", "orange"], ["black"], ["green", "orange"], ["white"]] == [["green", "orange"], ["black"], ["green", "orange"], ["white"]]
#guard sortSublists [["a","b"],["d","c"],["g","h"], ["f","e"]] == [["a", "b"], ["c", "d"], ["g", "h"], ["e", "f"]]
