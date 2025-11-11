import Batteries

open Std

def mulEvenOdd (list1 : List Int) : Int :=
  let first_even := list1.find? (fun el => el % 2 == 0)
  let first_odd := list1.find? (fun el => el % 2 != 0)
  let fe := match first_even with | some x => x | none => -1
  let fo := match first_odd with | some x => x | none => -1
  fe * fo

#guard mulEvenOdd [1,3,5,7,4,1,6,8] == 4
#guard mulEvenOdd [1,2,3,4,5,6,7,8,9,10] == 2
#guard mulEvenOdd [1,5,7,9,10] == 10
