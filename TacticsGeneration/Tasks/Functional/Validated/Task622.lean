import Batteries

open Std

def getMedian (arr1 arr2 : List Nat) (n : Nat) : Float := Id.run do
  let mut i := 0
  let mut j := 0
  let mut m1 : Int := -1
  let mut m2 : Int := -1
  for _ in [: n + 1] do
    if i == n then
      m1 := m2
      m2 := Int.ofNat (arr2.getD 0 0)
      break
    else if j == n then
      m1 := m2
      m2 := Int.ofNat (arr1.getD 0 0)
      break
    else
      let ai := arr1.getD i 0
      let aj := arr2.getD j 0
      if ai ≤ aj then
        m1 := m2
        m2 := Int.ofNat ai
        i := i + 1
      else
        m1 := m2
        m2 := Int.ofNat aj
        j := j + 1
  return Float.ofInt (m1 + m2) / 2.0

#guard getMedian [1, 12, 15, 26, 38] [2, 13, 17, 30, 45] 5 == 16.0
#guard getMedian [2, 4, 8, 9] [7, 13, 19, 28] 4 == 8.5
#guard getMedian [3, 6, 14, 23, 36, 42] [2, 18, 27, 39, 49, 55] 6 == 25.0
