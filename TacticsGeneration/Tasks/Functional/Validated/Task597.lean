import Batteries

open Std

def findKth (arr1 arr2 : List Nat) (m n k : Nat) : Nat := Id.run do
  
  
  let a1 := arr1.toArray
  let a2 := arr2.toArray
  let mut sorted1 := Array.replicate (m + n) 0
  let mut i := 0
  let mut j := 0
  let mut d := 0
  while i < m && j < n do
    if a1[i]! < a2[j]! then
      sorted1 := sorted1.set! d (a1[i]!)
      i := i + 1
    else
      sorted1 := sorted1.set! d (a2[j]!)
      j := j + 1
    d := d + 1
  while i < m do
    sorted1 := sorted1.set! d (a1[i]!)
    d := d + 1
    i := i + 1
  while j < n do
    sorted1 := sorted1.set! d (a2[j]!)
    d := d + 1
    j := j + 1
  return sorted1[k - 1]!

#guard findKth [2, 3, 6, 7, 9] [1, 4, 8, 10] 5 4 5 = 6
#guard findKth [100, 112, 256, 349, 770] [72, 86, 113, 119, 265, 445, 892] 5 7 7 = 256
#guard findKth [3, 4, 7, 8, 10] [2, 5, 9, 11] 5 4 6 = 8
