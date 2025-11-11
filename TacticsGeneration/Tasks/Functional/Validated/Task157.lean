import Batteries
open Std

noncomputable instance instDecidableEqFloat : DecidableEq Float := Classical.decEq _

def encodeList {α : Type} [DecidableEq α] (list1 : List α) : List (Nat × α) :=
  match list1 with
  | [] => []
  | x :: xs =>
    let rec go (current : α) (count : Nat) (rest : List α) (acc : List (Nat × α)) : List (Nat × α) :=
      match rest with
      | [] => ((count, current) :: acc).reverse
      | y :: ys =>
        match decEq y current with
        | isTrue _ => go current (count + 1) ys acc
        | isFalse _ => go y 1 ys ((count, current) :: acc)
    go x 1 xs []

#guard encodeList [1.0, 1.0, 2.0, 3.0, 4.0, 4.3, 5.0, 1.0] = [(2, 1.0), (1, 2.0), (1, 3.0), (1, 4.0), (1, 4.3), (1, 5.0), (1, 1.0)]
#guard encodeList ("automatically".data) = [(1, 'a'), (1, 'u'), (1, 't'), (1, 'o'), (1, 'm'), (1, 'a'), (1, 't'), (1, 'i'), (1, 'c'), (1, 'a'), (2, 'l'), (1, 'y')]
#guard encodeList ("python".data) = [(1, 'p'), (1, 'y'), (1, 't'), (1, 'h'), (1, 'o'), (1, 'n')]
