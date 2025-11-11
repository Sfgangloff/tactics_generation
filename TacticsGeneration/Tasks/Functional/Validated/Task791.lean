import Batteries

open Std

def remove_nested (test_tup : List (Sum Nat (List Nat))) : List Nat :=
  test_tup.foldl (init := []) (fun acc ele =>
    match ele with
    | Sum.inl n => acc ++ [n]
    | Sum.inr _ => acc
  )

#guard remove_nested [Sum.inl 1, Sum.inl 5, Sum.inl 7, Sum.inr [4, 6], Sum.inl 10] = [1, 5, 7, 10]
#guard remove_nested [Sum.inl 2, Sum.inl 6, Sum.inl 8, Sum.inr [5, 7], Sum.inl 11] = [2, 6, 8, 11]
#guard remove_nested [Sum.inl 3, Sum.inl 7, Sum.inl 9, Sum.inr [6, 8], Sum.inl 12] = [3, 7, 9, 12]
