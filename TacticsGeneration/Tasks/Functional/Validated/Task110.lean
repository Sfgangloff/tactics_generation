import Batteries
open Std

def extractMissing (testList : List (Nat × Nat)) (strtVal stopVal : Nat) : List (Nat × Nat) :=
  let rec loop (lst : List (Nat × Nat)) (strtVal : Nat) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
    match lst with
    | [] => acc
    | (s₀, s₁) :: subs =>
      if s₀ > strtVal then
        let newAcc := (strtVal, s₀) :: acc
        let newStrtVal := s₁
        loop subs newStrtVal newAcc
      else if strtVal < stopVal then
        let newAcc := (strtVal, stopVal) :: acc
        loop subs strtVal newAcc
      else
        acc
  loop testList strtVal []

#eval extractMissing [(6, 9), (15, 34), (48, 70)] 2 100 == [(2, 6), (9, 100), (9, 15), (34, 100), (34, 48), (70, 100)].reverse
#eval extractMissing [(7, 2), (15, 19), (38, 50)] 5 60 == [(5, 7), (2, 60), (2, 15), (19, 60), (19, 38), (50, 60)].reverse
#eval extractMissing [(7, 2), (15, 19), (38, 50)] 1 52 == [(1, 7), (2, 52), (2, 15), (19, 52), (19, 38), (50, 52)].reverse
