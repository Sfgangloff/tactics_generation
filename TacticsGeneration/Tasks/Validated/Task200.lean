import Batteries

open Std

def positionMax (list1 : List Nat) : List Nat :=
  
  let maxVal :=
    match list1 with
    | [] => 0
    | x :: xs => xs.foldl (fun m a => if a > m then a else m) x
  let (_, resRev) :=
    list1.foldl
      (fun (p : Nat × List Nat) (j : Nat) =>
        let (i, res) := p
        let res := if j == maxVal then i :: res else res
        (i+1, res))
      (0, [])
  resRev.reverse

#guard positionMax [12,33,23,10,67,89,45,667,23,12,11,10,54] == [7]
#guard positionMax [1,2,2,2,4,4,4,5,5,5,5] == [7,8,9,10]
#guard positionMax [2,1,5,6,8,3,4,9,10,11,8,12] == [11]
