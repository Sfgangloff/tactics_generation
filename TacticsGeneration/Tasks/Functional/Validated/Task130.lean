import Batteries

open Std

def updateCount (acc : List (Nat × Nat)) (x : Nat) : List (Nat × Nat) :=
  match acc with
  | [] => [(x, 1)]
  | (y, c) :: rest =>
    if x == y then
      (y, c + 1) :: rest
    else
      (y, c) :: updateCount rest x

def maxOccurrences (nums : List Nat) : Nat × Nat :=
  let counts := nums.foldl updateCount []
  match counts with
  | [] => (0, 0)
  | h :: t =>
    let best := t.foldl (fun (best : Nat × Nat) (p : Nat × Nat) =>
      let (curk, curc) := best
      let (k, c) := p
      if c > curc then (k, c) else best
    ) h
    best

#guard maxOccurrences [2,3,8,4,7,9,8,2,6,5,1,6,1,2,3,2,4,6,9,1,2] = (2, 5)
#guard maxOccurrences [2,3,8,4,7,9,8,7,9,15,14,10,12,13,16,16,18] = (8, 2)
#guard maxOccurrences [10,20,20,30,40,90,80,50,30,20,50,10] = (20, 3)
