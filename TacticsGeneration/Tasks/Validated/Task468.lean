import Batteries

open Std

 
def maxProduct (arr : List Nat) (n : Nat) : Nat := Id.run do
  let a := arr.toArray
  let mut mpis := Array.replicate n 0
  
  for i in [: n] do
    mpis := mpis.set! i (a[i]!)
  
  for i in [1 : n] do
    for j in [: i] do
      if a[i]! > a[j]! && mpis[i]! < mpis[j]! * a[i]! then
        mpis := mpis.set! i (mpis[j]! * a[i]!)
  
  let mut m := 0
  for i in [: n] do
    let v := mpis[i]!
    if v > m then m := v
  return m

#guard maxProduct [3, 100, 4, 5, 150, 6] 6 == 45000
#guard maxProduct [4, 42, 55, 68, 80] 5 == 50265600
#guard maxProduct [10, 22, 9, 33, 21, 50, 41, 60] 8 == 21780000
