import Batteries
open Std

def findRotationCount (A : List Int) : Int := Id.run do
  let n := A.length
  if n == 0 then
    return -1
  let rec loop (fuel : Nat) (left right : Int) : Int :=
    if fuel = 0 then
      -1
    else
      if left ≤ right then
        let leftNat := Int.toNat left
        let rightNat := Int.toNat right
        let aLeft := A.getD leftNat 0
        let aRight := A.getD rightNat 0
        if aLeft ≤ aRight then
          left
        else
          let mid := (left + right) / 2
          let midNat := Int.toNat mid
          let nextIdx := (midNat + 1) % n
          let prevIdx := (midNat + (n - 1)) % n
          let aMid := A.getD midNat 0
          let aNext := A.getD nextIdx 0
          let aPrev := A.getD prevIdx 0
          if aMid ≤ aNext && aMid ≤ aPrev then
            mid
          else if aMid ≤ aRight then
            loop (fuel - 1) left (mid - 1)
          else if aMid ≥ aLeft then
            loop (fuel - 1) (mid + 1) right
          else
            -1
      else
        -1
  let right0 := Int.ofNat (n - 1)
  return loop (n + 1) 0 right0

#guard findRotationCount [8, 9, 10, 1, 2, 3, 4, 5, 6, 7] = (3 : Int)
#guard findRotationCount [8, 9, 10, 2, 5, 6] = (3 : Int)
#guard findRotationCount [2, 5, 6, 8, 9, 10] = (0 : Int)
