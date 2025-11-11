import Batteries
open Std

def removeFirst (l : List Nat) (x : Nat) : List Nat :=
  match l with
  | [] => []
  | y :: ys => if y = x then ys else y :: removeFirst ys x

def nthD (l : List Nat) (n : Nat) (d : Nat) : Nat :=
  match l, n with
  | [], _ => d
  | x :: _, 0 => x
  | _ :: xs, n+1 => nthD xs n d

def remove_odd (l : List Nat) : List Nat := Id.run do
  let mut cur := l
  let mut idx : Nat := 0
  while idx < cur.length do
    let x := nthD cur idx 0
    if x % 2 ≠ 0 then
      
      cur := removeFirst cur x
      
      idx := idx + 1
    else
      idx := idx + 1
  return cur

#guard remove_odd [1, 2, 3] = [2]
#guard remove_odd [2, 4, 6] = [2, 4, 6]
#guard remove_odd [10, 20, 3] = [10, 20]
