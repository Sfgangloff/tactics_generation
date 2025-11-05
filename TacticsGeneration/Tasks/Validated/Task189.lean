import Batteries

open Std

def firstMissingPositive (arr : List Int) (n : Nat) : Nat := Id.run do
  
  let mut a : Array Int := arr.toArray
  let mut ptr : Nat := 0
  
  for i in [: n] do
    if a[i]! == 1 then
      ptr := 1
  if ptr == 0 then
    return 1
  
  for i in [: n] do
    let ai := a[i]!
    if ai ≤ 0 || ai > Int.ofNat n then
      a := a.set! i 1
  
  for i in [: n] do
    let ai := a[i]!
    
    let r : Int := (ai - 1) % (Int.ofNat n)
    let j : Nat := Int.toNat r
    let old := a[j]!
    a := a.set! j (old + Int.ofNat n)
  
  for i in [: n] do
    if a[i]! ≤ Int.ofNat n then
      return i + 1
  return n + 1

#guard firstMissingPositive [1, 2, 3, -1, 5] 5 = 4
#guard firstMissingPositive [0, -1, -2, 1, 5, 8] 6 = 2
#guard firstMissingPositive [0, 1, 2, 5, -8] 5 = 3
