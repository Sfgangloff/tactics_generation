import Batteries

open Std

def sum_Of_Subarray_Prod (arr : List Nat) (n : Nat) : Nat := Id.run do
  
  let mut ans := 0
  let mut res := 0
  let mut i := n
  while i > 0 do
    let j := i - 1
    let incr := arr.getD j 0 * (1 + res)
    ans := ans + incr
    res := incr
    i := j
  return ans

#guard sum_Of_Subarray_Prod [1,2,3] 3 = 20
#guard sum_Of_Subarray_Prod [1,2] 2 = 5
#guard sum_Of_Subarray_Prod [1,2,3,4] 4 = 84
