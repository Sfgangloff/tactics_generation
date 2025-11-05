import Batteries

open Std

def removeSubstr (s sub : String) : String :=
  (s.splitOn sub).foldl (fun acc part => acc ++ part) ""

def tupleStrInt (testStr : String) : List Int :=
  let s1 := removeSubstr testStr "("
  let s2 := removeSubstr s1 ")"
  let s3 := removeSubstr s2 "..."
  let parts := s3.splitOn ", "
  parts.map (fun num => (num.toInt?).getD 0)

#guard tupleStrInt "(7, 8, 9)" == [7, 8, 9]
#guard tupleStrInt "(1, 2, 3)" == [1, 2, 3]
#guard tupleStrInt "(4, 5, 6)" == [4, 5, 6]
