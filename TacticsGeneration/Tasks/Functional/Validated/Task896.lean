import Batteries

open Std

def last (n : Nat × Nat) : Nat := n.snd

private def insertByLast (x : Nat × Nat) (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  match xs with
  | [] => [x]
  | y :: ys =>
    if last x < last y then x :: xs else y :: insertByLast x ys

private def isortByLast (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  match xs with
  | [] => []
  | x :: xs' => insertByLast x (isortByLast xs')

def sort_list_last (tuples : List (Nat × Nat)) : List (Nat × Nat) :=
  isortByLast tuples

#guard sort_list_last [(2, 5), (1, 2), (4, 4), (2, 3), (2, 1)] == [(2, 1), (1, 2), (2, 3), (4, 4), (2, 5)]
#guard sort_list_last [(9, 8), (4, 7), (3, 5), (7, 9), (1, 2)] == [(1, 2), (3, 5), (4, 7), (9, 8), (7, 9)]
#guard sort_list_last [(20, 50), (10, 20), (40, 40)] == [(10, 20), (40, 40), (20, 50)]
