import Batteries

open Std

def diffEvenOdd (list1 : List Int) : Int :=
  let firstEven :=
    match list1.find? (fun el => el % 2 == 0) with
    | some el => el
    | none => -1
  let firstOdd :=
    match list1.find? (fun el => el % 2 != 0) with
    | some el => el
    | none => -1
  firstEven - firstOdd

#guard diffEvenOdd [1,3,5,7,4,1,6,8] = 3
#guard diffEvenOdd [1,2,3,4,5,6,7,8,9,10] = 1
#guard diffEvenOdd [1,5,7,9,10] = 9
