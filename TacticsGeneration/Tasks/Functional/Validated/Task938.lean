import Batteries

open Std

def findCloset (A B C : List Nat) (p q r : Nat) : Nat × Nat × Nat := Id.run do
  
  
  let a := A.toArray
  let b := B.toArray
  let c := C.toArray
  let mut diff : Nat := 1000000000
  let mut res_i := 0
  let mut res_j := 0
  let mut res_k := 0
  let mut i := 0
  let mut j := 0
  let mut k := 0
  let mut done := false
  while i < p && j < q && k < r && !done do
    let ai := a[i]!
    let bj := b[j]!
    let ck := c[k]!
    let minimum := min ai (min bj ck)
    let maximum := max ai (max bj ck)
    let d := maximum - minimum
    if d < diff then
      res_i := i
      res_j := j
      res_k := k
      diff := d
    if diff == 0 then
      done := true
    else
      if ai == minimum then
        i := i + 1
      else if bj == minimum then
        j := j + 1
      else
        k := k + 1
  return (a[res_i]!, b[res_j]!, c[res_k]!)

#guard findCloset [1, 4, 10] [2, 15, 20] [10, 12] 3 3 2 = (10, 15, 10)
#guard findCloset [20, 24, 100] [2, 19, 22, 79, 800] [10, 12, 23, 24, 119] 3 5 5 = (24, 22, 23)
#guard findCloset [2, 5, 11] [3, 16, 21] [11, 13] 3 3 2 = (11, 16, 11)
