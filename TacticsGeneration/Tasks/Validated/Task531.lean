import Batteries
open Std

def listGet? {α} (xs : List α) (i : Nat) : Option α :=
  let rec go (xs : List α) (i : Nat) : Option α :=
    match xs with
    | [] => none
    | x :: xs' =>
      match i with
      | 0 => some x
      | i+1 => go xs' i
  go xs i

def minCoins (coins : List Nat) (m : Nat) (V : Nat) : Nat :=
  let inf : Nat := 1000000000
  let coins' := coins.take m
  let dp :=
    Id.run do
      let mut dp : List Nat := [0]
      for v in [1:V+1] do
        let mut res := inf
        for ci in coins' do
          if ci ≠ 0 ∧ ci ≤ v then
            let sub := (listGet? dp (v - ci)).getD inf
            if sub ≠ inf ∧ sub + 1 < res then
              res := sub + 1
        dp := dp ++ [res]
      return dp
  (listGet? dp V).getD inf

#guard minCoins [9, 6, 5, 1] 4 11 = 2
#guard minCoins [4, 5, 6, 7, 8, 9] 6 9 = 1
#guard minCoins [1, 2, 3] 3 4 = 2
