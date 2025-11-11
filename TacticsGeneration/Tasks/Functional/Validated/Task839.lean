import Batteries
open Std

def bubblePass (l : List (String × Sum Nat String)) : List (String × Sum Nat String) :=
  match l with
  | [] => []
  | [a] => [a]
  | a :: b :: rest =>
    match compare a.fst b.fst with
    | .gt => b :: bubblePass (a :: rest)
    | _ => a :: bubblePass (b :: rest)

def sortTuple (tup : List (String × Sum Nat String)) : List (String × Sum Nat String) :=
  let rec loop (k : Nat) (l : List (String × Sum Nat String)) : List (String × Sum Nat String) :=
    match k with
    | 0 => l
    | k+1 => loop k (bubblePass l)
  loop tup.length tup

#guard sortTuple [("Amana", .inl 28), ("Zenat", .inl 30), ("Abhishek", .inl 29), ("Nikhil", .inl 21), ("B", .inr "C")] = [("Abhishek", .inl 29), ("Amana", .inl 28), ("B", .inr "C"), ("Nikhil", .inl 21), ("Zenat", .inl 30)]
#guard sortTuple [("aaaa", .inl 28), ("aa", .inl 30), ("bab", .inl 29), ("bb", .inl 21), ("csa", .inr "C")] = [("aa", .inl 30), ("aaaa", .inl 28), ("bab", .inl 29), ("bb", .inl 21), ("csa", .inr "C")]
#guard sortTuple [("Sarala", .inl 28), ("Ayesha", .inl 30), ("Suman", .inl 29), ("Sai", .inl 21), ("G", .inr "H")] = [("Ayesha", .inl 30), ("G", .inr "H"), ("Sai", .inl 21), ("Sarala", .inl 28), ("Suman", .inl 29)]
