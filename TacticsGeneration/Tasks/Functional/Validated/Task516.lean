import Batteries
open Std

def numPasses (m : Nat) : Nat :=
  if m == 0 then 0
  else
    Id.run do
      let mut t := m - 1
      let mut acc := 0
      while t != 0 do
        t := t / 10
        acc := acc + 1
      return acc

def radixSort (nums : List Nat) : List Nat := Id.run do
  match nums with
  | [] => return []
  | _ =>
    let maxDigit := nums.foldl (fun m x => if x > m then x else m) 0
    let passes := numPasses maxDigit
    let mut placement := 1
    let mut arr := nums.toArray
    for _ in [: passes] do
      let mut buckets : Array (Array Nat) := Array.replicate 10 #[]
      for i in arr do
        let tmp := (i / placement) % 10
        buckets := buckets.modify tmp (fun bucket => bucket.push i)
      let mut a := 0
      for b in [0:10] do
        let buck := buckets[b]!
        for x in buck do
          arr := arr.set! a x
          a := a + 1
      placement := placement * 10
    return arr.toList

#guard radixSort [15, 79, 25, 68, 37] = [15, 25, 37, 68, 79]
#guard radixSort [9, 11, 8, 7, 3, 2] = [2, 3, 7, 8, 9, 11]
#guard radixSort [36, 12, 24, 26, 29] = [12, 24, 26, 29, 36]
