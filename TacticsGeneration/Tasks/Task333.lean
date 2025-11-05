import Batteries
open Std

def minBySecond (l : List (String × Nat)) : Option (String × Nat) :=
  match l with
  | [] => none
  | x :: xs => some <| xs.foldl (fun acc y => if y.snd < acc.snd then y else acc) x

def removeFirst [DecidableEq α] (l : List α) (x : α) : List α :=
  match l with
  | [] => []
  | y :: ys => if decide (y = x) then ys else y :: removeFirst ys x

def «Sort» (sub_li : List (String × Nat)) : List (String × Nat) := Id.run do
  let n := sub_li.length
  let mut rem := sub_li
  let mut res : List (String × Nat) := []
  for _ in [: n] do
    match minBySecond rem with
    | none => break
    | some m =>
      rem := removeFirst rem m
      res := res ++ [m]
  return res

macro "Sort " x:term : term => `(Task333.«Sort» $x)

#guard Sort [("a", 10), ("b", 5), ("c", 20), ("d", 15)] = [("b", 5), ("a", 10), ("d", 15), ("c", 20)]
#guard Sort [("452", 10), ("256", 5), ("100", 20), ("135", 15)] = [("256", 5), ("452", 10), ("135", 15), ("100", 20)]
#guard Sort [("rishi", 10), ("akhil", 5), ("ramya", 20), ("gaur", 15)] = [("akhil", 5), ("rishi", 10), ("gaur", 15), ("ramya", 20)]
