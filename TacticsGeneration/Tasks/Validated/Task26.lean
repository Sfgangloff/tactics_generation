import Batteries
open Std

def checkKElements (testList : List (List Nat)) (k : Nat) : Bool :=
  let res :=
    testList.all fun tup =>
      tup.all fun ele => ele == k
  res

#guard checkKElements [[4, 4], [4, 4, 4], [4, 4], [4, 4, 4, 4], [4]] 4 == true
#guard checkKElements [[7, 7, 7], [7, 7]] 7 == true
#guard checkKElements [[9, 9], [9, 9, 9, 9]] 7 == false
#guard checkKElements [[4, 4], [4, 4, 4], [4, 4], [4, 4, 6, 4], [4]] 4 == false
