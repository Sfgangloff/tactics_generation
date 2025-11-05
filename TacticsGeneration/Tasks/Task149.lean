import Batteries
open Std

def longestSubseqWithDiffOne (arr : List Nat) (n : Nat) : Nat :=
  let a := arr.toArray
  let rec inner (i j rem : Nat) (dp : Array Nat) : Array Nat :=
    match rem with
    | 0 => dp
    | rem' + 1 =>
      let ai := a.get! i
      let aj := a.get! j
      let dp2 :=
        if ai == aj + 1 || aj == ai + 1 then
          let dpi := dp.get! i
          let dpj := dp.get! j
          let newVal := Nat.max dpi (dpj + 1)
          dp.set! i newVal
        else
          dp
      inner i (j + 1) rem' dp2
  let rec outer (i rem : Nat) (dp : Array Nat) : Array Nat :=
    match rem with
    | 0 => dp
    | rem' + 1 =>
      let dp2 := inner i 0 i dp
      outer (i + 1) rem' dp2
  let dp0 := Array.replicate n 1
  let dp := outer 0 n dp0
  let rec maxLoop (i rem : Nat) (res : Nat) : Nat :=
    match rem with
    | 0 => res
    | rem' + 1 =>
      let v := dp.get! i
      let res2 := if res < v then v else res
      maxLoop (i + 1) rem' res2
  maxLoop 0 n 1

#guard longestSubseqWithDiffOne [1, 2, 3, 4, 5, 3, 2] 7 = 6
#guard longestSubseqWithDiffOne [10, 9, 4, 5, 4, 8, 6] 7 = 3
#guard longestSubseqWithDiffOne [1, 2, 3, 2, 3, 7, 2, 1] 8 = 7
