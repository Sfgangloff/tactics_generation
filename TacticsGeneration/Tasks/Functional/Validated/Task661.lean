import Batteries
open Std

def maxSumOfThreeConsecutive (arr : List Nat) (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | _ =>
    match arr with
    | [] => 0
    | a0 :: t =>
      let dp0 := a0
      if n = 1 then
        dp0
      else
        match t with
        | [] => dp0
        | a1 :: u =>
          let dp1 := a0 + a1
          if n = 2 then
            dp1
          else
            match u with
            | [] => dp1
            | a2 :: v =>
              let dp2 := Nat.max dp1 (Nat.max (a1 + a2) (a0 + a2))
              if n = 3 then
                dp2
              else
                let rec go (i : Nat) (prev3dp prev2dp prev1dp prev1a : Nat) (rest : List Nat) : Nat :=
                  match rest with
                  | [] => prev1dp
                  | ai :: rest' =>
                    if i < n then
                      let dpi := Nat.max (Nat.max prev1dp (prev2dp + ai)) (ai + prev1a + prev3dp)
                      go (i + 1) prev2dp prev1dp dpi ai rest'
                    else
                      prev1dp
                go 3 dp0 dp1 dp2 a2 v

#guard maxSumOfThreeConsecutive [100, 1000, 100, 1000, 1] 5 = 2101
#guard maxSumOfThreeConsecutive [3000, 2000, 1000, 3, 10] 5 = 5013
#guard maxSumOfThreeConsecutive [1, 2, 3, 4, 5, 6, 7, 8] 8 = 27
