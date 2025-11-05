import Batteries
open Std

def siftDown (a : Array Nat) (start n : Nat) : Array Nat := Id.run do
  let mut arr := a
  let x := arr[start]!
  let mut i := start
  let mut j := 2 * i + 1
  while j < n do
    let mut smallest := j
    if j + 1 < n then
      if arr[j + 1]! < arr[j]! then
        smallest := j + 1
    if arr[smallest]! < x then
      arr := Array.set! arr i (arr[smallest]!)
      i := smallest
      j := 2 * i + 1
    else
      break
  arr := Array.set! arr i x
  return arr

def rawHeap (rawheap : List Nat) : List Nat := Id.run do
  let mut arr := rawheap.toArray
  let n := arr.size
  let mut i := n / 2
  while i > 0 do
    i := i - 1
    arr := siftDown arr i n
  return arr.toList

#guard rawHeap [25, 44, 68, 21, 39, 23, 89] == [21, 25, 23, 44, 39, 68, 89]
#guard rawHeap [25, 35, 22, 85, 14, 65, 75, 25, 58] == [14, 25, 22, 25, 35, 65, 75, 85, 58]
#guard rawHeap [4, 5, 6, 2] == [2, 4, 6, 5]
