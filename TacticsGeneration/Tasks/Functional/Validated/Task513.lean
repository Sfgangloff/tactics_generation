import Batteries
open Std

def addStr (test_tup : List Nat) (K : String) : List (Sum Nat String) :=
  List.foldr (fun sub acc => Sum.inl sub :: Sum.inr K :: acc) [] test_tup

#guard addStr [5, 6, 7, 4, 9] "FDF" = [Sum.inl 5, Sum.inr "FDF", Sum.inl 6, Sum.inr "FDF", Sum.inl 7, Sum.inr "FDF", Sum.inl 4, Sum.inr "FDF", Sum.inl 9, Sum.inr "FDF"]
#guard addStr [7, 8, 9, 10] "PF" = [Sum.inl 7, Sum.inr "PF", Sum.inl 8, Sum.inr "PF", Sum.inl 9, Sum.inr "PF", Sum.inl 10, Sum.inr "PF"]
#guard addStr [11, 14, 12, 1, 4] "JH" = [Sum.inl 11, Sum.inr "JH", Sum.inl 14, Sum.inr "JH", Sum.inl 12, Sum.inr "JH", Sum.inl 1, Sum.inr "JH", Sum.inl 4, Sum.inr "JH"]
