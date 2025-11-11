import Batteries

open Std

def consecutiveDuplicates [BEq α] (nums : List α) : List α :=
  let rec go (prev? : Option α) (xs : List α) (acc : List α) :=
    match xs with
    | [] => acc.reverse
    | x :: xs' =>
      match prev? with
      | some y =>
        if x == y then
          go prev? xs' acc
        else
          go (some x) xs' (x :: acc)
      | none =>
        go (some x) xs' (x :: acc)
  go none nums []

#guard consecutiveDuplicates [0, 0, 1, 2, 3, 4, 4, 5, 6, 6, 6, 7, 8, 9, 4, 4] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 4]
#guard consecutiveDuplicates [10, 10, 15, 19, 18, 18, 17, 26, 26, 17, 18, 10] = [10, 15, 19, 18, 17, 26, 17, 18, 10]
#guard consecutiveDuplicates ["a", "a", "b", "c", "d", "d"] = ["a", "b", "c", "d"]
