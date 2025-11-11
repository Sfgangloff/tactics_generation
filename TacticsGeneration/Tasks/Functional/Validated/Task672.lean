import Batteries

open Std

def maxOfThree (num1 num2 num3 : Nat) : Nat :=
  if num1 >= num2 && num1 >= num3 then
    num1
  else if num2 >= num1 && num2 >= num3 then
    num2
  else
    num3

#guard maxOfThree 10 20 30 = 30
#guard maxOfThree 55 47 39 = 55
#guard maxOfThree 10 49 30 = 49
