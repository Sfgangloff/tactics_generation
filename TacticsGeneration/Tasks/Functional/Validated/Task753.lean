import Batteries

open Std

def findMinBySnd? (xs : List (String × Nat)) : Option (String × Nat) :=
  match xs with
  | [] => none
  | h :: t =>
    some <| t.foldl (fun acc x => if x.snd < acc.snd then x else acc) h

def selectKBySnd (xs : List (String × Nat)) (k : Nat) : List (String × Nat) :=
  match k with
  | 0 => []
  | k+1 =>
    match findMinBySnd? xs with
    | none => []
    | some m => m :: selectKBySnd (xs.erase m) k

def min_k (test_list : List (String × Nat)) (K : Nat) : List (String × Nat) :=
  selectKBySnd test_list K

#guard min_k [("Manjeet", 10), ("Akshat", 4), ("Akash", 2), ("Nikhil", 8)] 2 == [("Akash", 2), ("Akshat", 4)]
#guard min_k [("Sanjeev", 11), ("Angat", 5), ("Akash", 3), ("Nepin", 9)] 3 == [("Akash", 3), ("Angat", 5), ("Nepin", 9)]
#guard min_k [("tanmay", 14), ("Amer", 11), ("Ayesha", 9), ("SKD", 16)] 1 == [("Ayesha", 9)]
