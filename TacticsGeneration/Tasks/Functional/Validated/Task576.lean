import Batteries
open Std

def is_Sub_Array (A B : List Nat) (n m : Nat) : Bool :=
  let arr := A.toArray
  let brr := B.toArray
  let fuel0 := (n + 1) * (m + 1) + 1
  let rec loop (i j : Nat) : Nat → Bool
    | 0 => false
    | fuel + 1 =>
      if i < n && j < m then
        if arr[i]! == brr[j]! then
          let i' := i + 1
          let j' := j + 1
          if j' == m then true else loop i' j' fuel
        else
          let i' := (i - j) + 1
          let j' := 0
          loop i' j' fuel
      else
        false
  loop 0 0 fuel0

#guard is_Sub_Array [1,4,3,5] [1,2] 4 2 == false
#guard is_Sub_Array [1,2,1] [1,2,1] 3 3 == true
#guard is_Sub_Array [1,0,2,2] [2,2,0] 4 3 == false
