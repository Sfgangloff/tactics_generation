import Batteries
open Std

private def listGet? (xs : List α) (i : Nat) : Option α :=
  match xs, i with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs', i+1 => listGet? xs' i

def maxProduct (arr : List Int) : Sum String (Int × Int) := Id.run do
  let arrLen := arr.length
  if arrLen < 2 then
    return Sum.inl "No pairs exists"
  let init :=
    match arr with
    | x :: y :: _ => (x, y)
    | _ => (0, 0)
  let mut x : Int := init.fst
  let mut y : Int := init.snd
  for i in [0:arrLen] do
    for j in [i+1:arrLen] do
      let a := (listGet? arr i).getD (0 : Int)
      let b := (listGet? arr j).getD (0 : Int)
      if a * b > x * y then
        x := a
        y := b
  return Sum.inr (x, y)

#guard maxProduct [1,2,3,4,7,0,8,4] == Sum.inr (7,8)
#guard maxProduct [0,-1,-2,-4,5,0,-6] == Sum.inr (-4,-6)
#guard maxProduct [1,2,3] == Sum.inr (2,3)
