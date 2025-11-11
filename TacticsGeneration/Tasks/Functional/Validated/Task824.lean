import Batteries
open Std

def removeFirst (l : List Nat) (x : Nat) : List Nat :=
  match l with
  | [] => []
  | y :: ys => if y == x then ys else y :: removeFirst ys x

def getAt? {α : Type u} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, Nat.succ j => getAt? xs j

def removeEven (l : List Nat) : List Nat := Id.run do
  let mut arr := l
  let mut idx := 0
  while idx < arr.length do
    match getAt? arr idx with
    | none => break
    | some i =>
      if i % 2 == 0 then
        arr := removeFirst arr i
      idx := idx + 1
  return arr

#guard removeEven [1, 3, 5, 2] = [1, 3, 5]
#guard removeEven [5, 6, 7] = [5, 7]
#guard removeEven [1, 2, 3, 4] = [1, 3]
