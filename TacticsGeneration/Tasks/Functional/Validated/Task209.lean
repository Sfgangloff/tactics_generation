import Batteries

open Std

private def siftDown (arr : Array Nat) (i n : Nat) : Array Nat := Id.run do
  let mut a := arr
  let mut idx := i
  while true do
    let left := 2*idx + 1
    if left >= n then
      break
    let right := left + 1
    let c :=
      if right < n && a[right]! < a[left]! then right else left
    if a[idx]! <= a[c]! then
      break
    else
      let ai := a[idx]!
      let ac := a[c]!
      a := a.set! idx ac
      a := a.set! c ai
      idx := c
  return a

private def heapify (arr : Array Nat) : Array Nat := Id.run do
  let mut a := arr
  let n := a.size
  let mut i := n / 2
  while i > 0 do
    i := i - 1
    a := siftDown a i n
  return a

def heapReplace (heap : List Nat) (a : Nat) : List Nat := Id.run do
  let mut ar := heap.toArray
  ar := heapify ar
  if ar.size = 0 then
    return []
  ar := ar.set! 0 a
  ar := siftDown ar 0 ar.size
  return ar.toList

#guard heapReplace [25, 44, 68, 21, 39, 23, 89] 21 == [21, 25, 23, 44, 39, 68, 89]
#guard heapReplace [25, 44, 68, 21, 39, 23, 89] 110 == [23, 25, 68, 44, 39, 110, 89]
#guard heapReplace [25, 44, 68, 21, 39, 23, 89] 500 == [23, 25, 68, 44, 39, 500, 89]
