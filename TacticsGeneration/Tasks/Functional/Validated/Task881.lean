import Batteries

open Std

def sumEvenOdd (list1 : List Int) : Int :=
  let rec firstWith (l : List Int) (p : Int → Bool) : Int :=
    match l with
    | [] => -1
    | x :: xs => if p x then x else firstWith xs p
  let first_even := firstWith list1 (fun el => el % 2 == 0)
  let first_odd := firstWith list1 (fun el => el % 2 != 0)
  first_even + first_odd

#guard sumEvenOdd [1, 3, 5, 7, 4, 1, 6, 8] == 5
#guard sumEvenOdd [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] == 3
#guard sumEvenOdd [1, 5, 7, 9, 10] == 11
