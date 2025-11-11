import Batteries

open Std

def min_Ops (arr : List Nat) (n k : Nat) : Int := Id.run do
  
  let xs := arr.take n
  let max1 := xs.foldl (fun m x => if m < x then x else m) 0
  let mut res : Int := 0
  for x in xs do
    if (max1 - x) % k != 0 then
      return (-1)
    else
      res := res + Int.ofNat ((max1 - x) / k)
  return res

#guard min_Ops [2,2,2,2] 4 3 == (0 : Int)
#guard min_Ops [4,2,6,8] 4 3 == (-1 : Int)
#guard min_Ops [21,33,9,45,63] 5 6 == (24 : Int)
