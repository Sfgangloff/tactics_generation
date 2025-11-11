import Batteries

open Std

def binarySearch (itemList : List Nat) (item : Nat) : Bool :=
  let len := itemList.length
  let last : Int := Int.ofNat len - 1
  let rec loop (first : Int) (last : Int) (found : Bool) (fuel : Nat) : Bool :=
    if fuel = 0 then found else
    if first <= last && !found then
      let mid : Int := (first + last) / 2
      let midNat : Nat := Int.toNat mid
      let midVal : Nat := itemList.getD midNat 0
      if midVal = item then
        true
      else if item < midVal then
        loop first (mid - 1) false (fuel - 1)
      else
        loop (mid + 1) last false (fuel - 1)
    else found
  loop 0 last false (len + 1)

#guard binarySearch [1,2,3,5,8] 6 == false
#guard binarySearch [7,8,9,10,13] 10 == true
#guard binarySearch [11,13,14,19,22,36] 23 == false
