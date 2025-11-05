import Batteries
open Std

def charToString (c : Char) : String := String.mk [c]

structure Info where
  count : Nat
  first : Nat

def mostCommonElem (s : String) (a : Nat) : List (String × Nat) := Id.run do
  
  let chars := s.data
  let mut m : Std.HashMap Char Info := Std.HashMap.empty
  let mut i := 0
  for c in chars do
    let old := m.find? c
    let newInfo :=
      match old with
      | none => { count := 1, first := i }
      | some inf => { count := inf.count + 1, first := inf.first }
    m := m.insert c newInfo
    i := i + 1
  
  let mut res : Array (String × Nat) := #[]
  let mut t := 0
  while t < a do
    let mut has := false
    let mut bestK : Char := 'a'
    let mut bestInfo : Info := { count := 0, first := 0 }
    let entries := m.toList
    for (k, inf) in entries do
      if !has then
        has := true
        bestK := k
        bestInfo := inf
      else
        let better :=
          if inf.count > bestInfo.count then true
          else if inf.count < bestInfo.count then false
          else inf.first < bestInfo.first
        if better then
          bestK := k
          bestInfo := inf
    if !has then
      break
    res := res.push (charToString bestK, bestInfo.count)
    m := m.erase bestK
    t := t + 1
  return res.toList

#guard mostCommonElem "lkseropewdssafsdfafkpwe" 3 == [("s", 4), ("e", 3), ("f", 3)]
#guard mostCommonElem "lkseropewdssafsdfafkpwe" 2 == [("s", 4), ("e", 3)]
#guard mostCommonElem "lkseropewdssafsdfafkpwe" 7 == [("s", 4), ("e", 3), ("f", 3), ("k", 2), ("p", 2), ("w", 2), ("d", 2)]
