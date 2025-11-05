import Batteries

open Std

def lbs (arr : List Nat) : Nat := Id.run do
  let n := arr.length
  let arrA := arr.toArray
  let mut lis := Array.replicate (n+1) 1
  for i in [1 : n] do
    for j in [0 : i] do
      if arrA[i]! > arrA[j]! && lis[i]! < lis[j]! + 1 then
        lis := lis.set! i (lis[j]! + 1)
  let mut lds := Array.replicate (n+1) 1
  if n >= 2 then
    for k in [0 : n-1] do
      let i := (n-2) - k
      for j in [i+1 : n] do
        if arrA[i]! > arrA[j]! && lds[i]! < lds[j]! + 1 then
          lds := lds.set! i (lds[j]! + 1)
  let mut maximum := lis[0]! + lds[0]! - 1
  for i in [1 : n] do
    let cand := lis[i]! + lds[i]! - 1
    maximum := if cand > maximum then cand else maximum
  return maximum

#guard lbs [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15] = 7
#guard lbs [1, 11, 2, 10, 4, 5, 2, 1] = 6
#guard lbs [80, 60, 30, 40, 20, 10] = 5
