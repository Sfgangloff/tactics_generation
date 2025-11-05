import Batteries

open Std

def combSort (nums : List Nat) : List Nat := Id.run do
  let mut arr := nums.toArray
  let mut gaps : Nat := arr.size
  let mut swapped : Bool := true
  let mut i : Nat := 0
  while gaps > 1 || swapped do
    gaps := (gaps * 10) / 13
    swapped := false
    i := 0
    while gaps + i < arr.size do
      let a := arr[i]!
      let b := arr[i + gaps]!
      if a > b then
        arr := arr.set! i b
        arr := arr.set! (i + gaps) a
        swapped := true
      i := i + 1
  return arr.toList

#guard combSort [5, 15, 37, 25, 79] == [5, 15, 25, 37, 79]
#guard combSort [41, 32, 15, 19, 22] == [15, 19, 22, 32, 41]
#guard combSort [99, 15, 13, 47] == [13, 15, 47, 99]
