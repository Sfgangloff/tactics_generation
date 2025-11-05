import Batteries

open Std

def findCombinations (test_list : List (Nat × Nat)) : List (Nat × Nat) :=
  let rec go (l : List (Nat × Nat)) : List (Nat × Nat) :=
    match l with
    | [] => []
    | x :: xs =>
      let fromX := xs.map (fun y =>
        match x, y with
        | (a1, a2), (b1, b2) => (b1 + a1, b2 + a2))
      fromX ++ go xs
  go test_list

#guard findCombinations [(2, 4), (6, 7), (5, 1), (6, 10)] = [(8, 11), (7, 5), (8, 14), (11, 8), (12, 17), (11, 11)]
#guard findCombinations [(3, 5), (7, 8), (6, 2), (7, 11)] = [(10, 13), (9, 7), (10, 16), (13, 10), (14, 19), (13, 13)]
#guard findCombinations [(4, 6), (8, 9), (7, 3), (8, 12)] = [(12, 15), (11, 9), (12, 18), (15, 12), (16, 21), (15, 15)]
