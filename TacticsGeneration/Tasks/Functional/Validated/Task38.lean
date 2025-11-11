import Batteries

open Std

def divEvenOdd (list1 : List Int) : Int :=
  let firstEven := list1.find? (fun el => el % 2 == 0) |>.getD (-1)
  let firstOdd := list1.find? (fun el => el % 2 != 0) |>.getD (-1)
  firstEven / firstOdd

#guard divEvenOdd [1,3,5,7,4,1,6,8] == 4
#guard divEvenOdd [1,2,3,4,5,6,7,8,9,10] == 2
#guard divEvenOdd [1,5,7,9,10] == 10
