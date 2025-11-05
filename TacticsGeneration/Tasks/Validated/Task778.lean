import Batteries

open Std

def packConsecutiveDuplicates {α : Type} [BEq α] (list1 : List α) : List (List α) :=
  let (resAcc, curr) :=
    list1.foldl
      (fun (state : List (List α) × List α) (x : α) =>
        let resAcc := state.fst
        let curr := state.snd
        match curr with
        | [] => (resAcc, [x])
        | y :: _ =>
          if x == y then (resAcc, x :: curr) else ((curr.reverse) :: resAcc, [x]))
      ([], [])
  let resAcc := if curr.isEmpty then resAcc else (curr.reverse) :: resAcc
  resAcc.reverse

#guard packConsecutiveDuplicates [0, 0, 1, 2, 3, 4, 4, 5, 6, 6, 6, 7, 8, 9, 4, 4] = [[0, 0], [1], [2], [3], [4, 4], [5], [6, 6, 6], [7], [8], [9], [4, 4]]
#guard packConsecutiveDuplicates [10, 10, 15, 19, 18, 18, 17, 26, 26, 17, 18, 10] = [[10, 10], [15], [19], [18, 18], [17], [26, 26], [17], [18], [10]]
#guard packConsecutiveDuplicates ["a", "a", "b", "c", "d", "d"] = [["a", "a"], ["b"], ["c"], ["d", "d"]]
