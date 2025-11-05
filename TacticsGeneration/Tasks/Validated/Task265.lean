import Batteries

open Std

def takeEveryFrom {α : Type} (S : List α) (offset step : Nat) : List α := Id.run do
  if step = 0 then return []
  let mut i := 0
  let mut res : Array α := #[]
  for x in S do
    if i % step == offset then
      res := res.push x
    i := i + 1
  return res.toList

def listSplit {α : Type} (S : List α) (step : Nat) : List (List α) :=
  if step = 0 then []
  else (List.range step).map (fun i => takeEveryFrom S i step)

#guard listSplit ["a","b","c","d","e","f","g","h","i","j","k","l","m","n"] 3 == [["a","d","g","j","m"],["b","e","h","k","n"],["c","f","i","l"]]
#guard listSplit [1,2,3,4,5,6,7,8,9,10,11,12,13,14] 3 == [[1,4,7,10,13],[2,5,8,11,14],[3,6,9,12]]
#guard listSplit ["python","java","C","C++","DBMS","SQL"] 2 == [["python","C","DBMS"],["java","C++","SQL"]]
