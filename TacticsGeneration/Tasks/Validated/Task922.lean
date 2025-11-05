import Batteries
open Std

def maxProduct (arr : List Int) : Option (Int × Int) :=
  match arr with
  | x :: y :: t =>
    let rec pairMaxWith (a : Int) (lst : List Int) (best : Int × Int) : Int × Int :=
      match lst with
      | [] => best
      | b :: bs =>
        let best' := if a * b > best.fst * best.snd then (a, b) else best
        pairMaxWith a bs best'
    let rec outer (lst : List Int) (best : Int × Int) : Int × Int :=
      match lst with
      | [] => best
      | [_] => best
      | a :: bs =>
        let best' := pairMaxWith a bs best
        outer bs best'
    let best0 := (x, y)
    let best := outer (x :: y :: t) best0
    some best
  | _ => none

#guard maxProduct [1, 2, 3, 4, 7, 0, 8, 4] == some (7, 8)
#guard maxProduct [0, -1, -2, -4, 5, 0, -6] == some (-4, -6)
#guard maxProduct [1, 3, 5, 6, 8, 9] == some (8, 9)
