import Batteries

open Std

def convertListDictionary (l1 l2 : List String) (l3 : List Nat) : List (List (String × (List (String × Nat)))) :=
  let rec go (a b : List String) (c : List Nat) : List (List (String × (List (String × Nat)))) :=
    match a, b, c with
    | x::xs, y::ys, z::zs => [ (x, [ (y, z) ]) ] :: go xs ys zs
    | _, _, _ => []
  go l1 l2 l3

#guard convertListDictionary ["S001", "S002", "S003", "S004"] ["Adina Park", "Leyton Marsh", "Duncan Boyle", "Saim Richards"] [85, 98, 89, 92]
  = [[("S001", [("Adina Park", 85)])], [("S002", [("Leyton Marsh", 98)])], [("S003", [("Duncan Boyle", 89)])], [("S004", [("Saim Richards", 92)])]]
#guard convertListDictionary ["abc","def","ghi","jkl"] ["python","program","language","programs"] [100,200,300,400]
  = [[("abc", [("python", 100)])], [("def", [("program", 200)])], [("ghi", [("language", 300)])], [("jkl", [("programs", 400)])]]
#guard convertListDictionary ["A1","A2","A3","A4"] ["java","C","C++","DBMS"] [10,20,30,40]
  = [[("A1", [("java", 10)])], [("A2", [("C", 20)])], [("A3", [("C++", 30)])], [("A4", [("DBMS", 40)])]]
