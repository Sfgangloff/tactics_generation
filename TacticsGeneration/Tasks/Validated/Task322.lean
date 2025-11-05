import Batteries

open Std

def positionMin (list1 : List Nat) : List Nat :=
  match list1 with
  | [] => []  
  | x :: xs =>
    let minVal := xs.foldl (fun acc y => if y < acc then y else acc) x
    let rec collect (l : List Nat) (i : Nat) (acc : List Nat) : List Nat :=
      match l with
      | [] => acc
      | y :: ys =>
        let acc' := if y == minVal then i :: acc else acc
        collect ys (i + 1) acc'
    (collect list1 0 []).reverse

#guard positionMin [12,33,23,10,67,89,45,667,23,12,11,10,54] = [3,11]
#guard positionMin [1,2,2,2,4,4,4,5,5,5,5] = [0]
#guard positionMin [2,1,5,6,8,3,4,9,10,11,8,12] = [1]
