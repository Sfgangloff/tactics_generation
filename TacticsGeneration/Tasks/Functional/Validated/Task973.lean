import Batteries

open Std

def leftRotate (s : String) (d : Nat) : String :=
  let tmp := s.drop d ++ s.take d
  tmp

#guard leftRotate "python" 2 == "thonpy"
#guard leftRotate "bigdata" 3 == "databig"
#guard leftRotate "hadoop" 1 == "adooph"
