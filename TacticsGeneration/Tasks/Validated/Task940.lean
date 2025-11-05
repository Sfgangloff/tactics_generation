import Batteries

open Std

def shift_down (arr : Array Nat) (start end_ : Nat) : Array Nat := Id.run do
  let mut a := arr
  let mut root := start
  while true do
    if hcond : root * 2 + 1 ≤ end_ then
      let mut child := root * 2 + 1
      if h2 : child + 1 ≤ end_ then
        if a[child]! < a[child + 1]! then
          child := child + 1
      else
        ()
      if h3 : child ≤ end_ then
        if a[root]! < a[child]! then
          let tmp := a[root]!
          a := a.set! root (a[child]!)
          a := a.set! child tmp
          root := child
        else
          return a
      else
        return a
    else
      break
  return a

def heapify (arr : Array Nat) : Array Nat := Id.run do
  let n := arr.size
  let end_ := match n with
    | 0 => 0
    | k+1 => k
  let mut a := arr
  match n with
  | 0 => return a
  | _ =>
    let mut start := n / 2
    while true do
      a := shift_down a start end_
      if h : start = 0 then
        break
      else
        start := start - 1
    return a

def heap_sort (arr : List Nat) : List Nat := Id.run do
  let mut a := arr.toArray
  a := heapify a
  let n := a.size
  let mut end_ := match n with
    | 0 => 0
    | k+1 => k
  while true do
    if h : end_ = 0 then
      break
    else
      let tmp := a[0]!
      a := a.set! 0 (a[end_]!)
      a := a.set! end_ tmp
      a := shift_down a 0 (end_ - 1)
      end_ := end_ - 1
  return a.toList

#guard heap_sort [12, 2, 4, 5, 2, 3] = [2, 2, 3, 4, 5, 12]
#guard heap_sort [32, 14, 5, 6, 7, 19] = [5, 6, 7, 14, 19, 32]
#guard heap_sort [21, 15, 29, 78, 65] = [15, 21, 29, 65, 78]
