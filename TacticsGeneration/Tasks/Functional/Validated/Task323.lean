import Batteries

open Std

def right_rotate (arr : List Int) (n : Nat) (out_of_place : Nat) (cur : Nat) : List Int := Id.run do
  let mut a := arr.toArray
  let temp := a[cur]!
  let mut i := cur
  while i > out_of_place do
    a := a.set! i (a[i-1]!)
    i := i - 1
  a := a.set! out_of_place temp
  return a.toList

def re_arrange (arr : List Int) (n : Nat) : List Int := Id.run do
  
  let mut a := arr
  let mut out_of_place : Int := -1
  for index in [0 : n] do
    if out_of_place >= 0 then
      let opNat := Int.toNat out_of_place
      let ai := a.getD index 0
      let aop := a.getD opNat 0
      if ((ai >= 0 && aop < 0) || (ai < 0 && aop >= 0)) then
        a := right_rotate a n opNat index
        let diff : Int := (Int.ofNat index) - out_of_place
        if diff > 2 then
          out_of_place := out_of_place + 2
        else
          out_of_place := -1
    if out_of_place == -1 then
      let ai2 := a.getD index 0
      if ((ai2 >= 0 && index % 2 == 0) || (ai2 < 0 && index % 2 == 1)) then
        out_of_place := Int.ofNat index
  return a

#guard re_arrange [-5, -2, 5, 2, 4, 7, 1, 8, 0, -8] 10 = [-5, 5, -2, 2, -8, 4, 7, 1, 8, 0]
#guard re_arrange [1, 2, 3, -4, -1, 4] 6 = [-4, 1, -1, 2, 3, 4]
#guard re_arrange [4, 7, 9, 77, -4, 5, -3, -9] 8 = [-4, 4, -3, 7, -9, 9, 77, 5]
