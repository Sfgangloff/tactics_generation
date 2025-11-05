import Batteries
open Std

private def onePass (xs : List (Nat × Nat)) : List (Nat × Nat) × Bool :=
  match xs with
  | [] => ([], False)
  | a :: rest =>
    let rec aux (acc : List (Nat × Nat)) (cur : Nat × Nat) (rest : List (Nat × Nat)) (changed : Bool) :
        List (Nat × Nat) × Bool :=
      match rest with
      | [] => ((acc.reverse) ++ [cur], changed)
      | b :: rs =>
        if cur.snd > b.snd then
          aux (b :: acc) cur rs True
        else
          aux (cur :: acc) b rs changed
    aux [] a rest False

def sortTuple (tup : List (Nat × Nat)) : List (Nat × Nat) :=
  let rec iter (n : Nat) (xs : List (Nat × Nat)) : List (Nat × Nat) :=
    match n with
    | 0 => xs
    | n' + 1 =>
      let (ys, changed) := onePass xs
      if changed then
        iter n' ys
      else
        ys
  iter tup.length tup

#guard sortTuple [(1, 3), (3, 2), (2, 1)] == [(2, 1), (3, 2), (1, 3)]
#guard sortTuple [(2, 4), (3, 3), (1, 1)] == [(1, 1), (3, 3), (2, 4)]
#guard sortTuple [(3, 9), (6, 7), (4, 3)] == [(4, 3), (6, 7), (3, 9)]
