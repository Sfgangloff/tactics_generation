import Batteries

open Std

def chkList (lst : List String) : Bool :=
  match lst with
  | [] => false
  | x :: xs => xs.all (fun y => y == x)

#guard chkList ["one","one","one"] == true
#guard chkList ["one","Two","Three"] == false
#guard chkList ["bigdata","python","Django"] == false
