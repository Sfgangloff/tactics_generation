import Batteries
open Std

def listGet? {α : Type u} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, Nat.succ i => listGet? xs i

def countPairs (arr : List Nat) (n : Nat) : Nat := Id.run do
  let mut cnt := 0
  for i in [0 : n] do
    for j in [i+1 : n] do
      let ai := (listGet? arr i).getD 0
      let aj := (listGet? arr j).getD 0
      if ai == aj then
        pure ()
      else
        cnt := cnt + 1
  return cnt

#guard countPairs [1,2,1] 3 = 2
#guard countPairs [1,1,1,1] 4 = 0
#guard countPairs [1,2,3,4,5] 5 = 10
