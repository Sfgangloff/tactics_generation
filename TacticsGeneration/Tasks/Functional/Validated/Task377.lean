import Batteries

open Std

def remove_Char (s : String) (c : Char) : String :=
  let counts := s.toList.foldl (fun acc ch => if ch == c then acc + 1 else acc) 0
  let lst0 := s.toList
  let rec loop (lst : List Char) (k : Nat) : List Char :=
    match k with
    | 0 => lst
    | Nat.succ k' => loop (lst.erase c) k'
  let lst' := loop lst0 counts
  String.mk lst'

#guard remove_Char "aba" 'a' == "b"
#guard remove_Char "toggle" 'g' == "tole"
#guard remove_Char "aabbc" 'b' == "aac"
