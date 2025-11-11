import Batteries

open Std

def wordLen (s : String) : Bool :=
  let words := s.splitOn " "
  match words with
  | [] => false
  | word::_ => word.length % 2 != 0

#guard wordLen "Hadoop" == false
#guard wordLen "great" == true
#guard wordLen "structure" == true
