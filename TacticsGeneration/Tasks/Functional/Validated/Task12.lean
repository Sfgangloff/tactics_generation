import Batteries
open Std

def insert {α : Type} (cmp : α → α → Bool) (x : α) : List α → List α
  | []      => [x]
  | y :: ys => if cmp x y then x :: y :: ys else y :: insert cmp x ys

def isort {α : Type} (cmp : α → α → Bool) : List α → List α
  | []       => []
  | x :: xs  => insert cmp x (isort cmp xs)

def sortMatrix (M : List (List Int)) : List (List Int) :=
  isort (fun a b => a.foldl (· + ·) 0 < b.foldl (· + ·) 0) M

#eval sortMatrix [[1, 2, 3], [2, 4, 5], [1, 1, 1]] 
#eval sortMatrix [[1, 2, 3], [-2, 4, -5], [1, -1, 1]] 
#eval sortMatrix [[5, 8, 9], [6, 4, 3], [2, 1, 4]]
