import Batteries

open Std

def get_Position (a : List Nat) (n m : Nat) : Nat := Id.run do
  let mut arr := a.toArray
  for i in [0 : n] do
    let ai := arr[i]!
    let rem := ai % m
    let add := if rem != 0 then 1 else 0
    let newv := ai / m + add
    arr := arr.set! i newv
  let mut result : Int := -1
  let mut maxx : Int := -1
  for t in [0 : n] do
    let i := n - 1 - t
    let v := Int.ofNat (arr[i]!)
    if maxx < v then
      maxx := v
      result := Int.ofNat i
  return Int.toNat (result + 1)

#guard get_Position [2,5,4] 3 2 = 2
#guard get_Position [4,3] 2 2 = 2
#guard get_Position [1,2,3,4] 4 1 = 4
