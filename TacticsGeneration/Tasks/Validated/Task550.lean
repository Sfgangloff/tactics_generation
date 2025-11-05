import Batteries

open Std

partial def find_Max (arr : List Nat) (low high : Nat) : Nat :=
  let a := arr.toArray
  if high < low then
    a[0]!
  else if high == low then
    a[low]!
  else
    let mid := low + (high - low) / 2
    if mid < high && a[mid + 1]! < a[mid]! then
      a[mid]!
    else if mid > low && a[mid]! < a[mid - 1]! then
      a[mid - 1]!
    else if a[low]! > a[mid]! then
      find_Max arr low (mid - 1)
    else
      find_Max arr (mid + 1) high

#guard find_Max [2,3,5,6,9] 0 4 = 9
#guard find_Max [3,4,5,2,1] 0 4 = 5
#guard find_Max [1,2,3] 0 2 = 3
