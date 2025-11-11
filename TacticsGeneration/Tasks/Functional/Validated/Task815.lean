import Batteries
open Std

def sortByDnf (arr : List Nat) (n : Nat) : List Nat :=
  let (z, o, t) := count (arr.take n) 0 0 0
  List.replicate z 0 ++ List.replicate o 1 ++ List.replicate t 2
where
  count (l : List Nat) (z o t : Nat) : Nat × Nat × Nat :=
    match l with
    | [] => (z, o, t)
    | x :: xs =>
      if x = 0 then
        count xs (z + 1) o t
      else if x = 1 then
        count xs z (o + 1) t
      else
        count xs z o (t + 1)

#guard sortByDnf [1,2,0,1,0,1,2,1,1] 9 == [0, 0, 1, 1, 1, 1, 1, 2, 2]
#guard sortByDnf [1,0,0,1,2,1,2,2,1,0] 10 == [0, 0, 0, 1, 1, 1, 1, 2, 2, 2]
#guard sortByDnf [2,2,1,0,0,0,1,1,2,1] 10 == [0, 0, 0, 1, 1, 1, 1, 2, 2, 2]
