import Batteries

open Std

def swapList (newList : List Nat) : List Nat := Id.run do
  
  let size := newList.length
  let mut arr := newList.toArray
  let temp := arr[0]!
  arr := arr.set! 0 arr[size - 1]!
  arr := arr.set! (size - 1) temp
  return arr.toList

#guard swapList [1, 2, 3] = [3, 2, 1]
#guard swapList [1, 2, 3, 4, 4] = [4, 2, 3, 4, 1]
#guard swapList [4, 5, 6] = [6, 5, 4]
