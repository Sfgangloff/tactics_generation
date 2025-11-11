import Batteries



/-!
  Auto-generated from task 9.
  Module: Task9
-/

open Std

namespace Task9

-- Find the minimum number of rotations required to get the same string
-- Uses String operations: length, drop, take, and concatenation.
-- Mirrors Python loop: for i in range(1, n+1)
-- If str == (str+str)[i:i+n] then return i, else return n
def find_Rotations (str : String) : Nat := Id.run do
  let tmp := str ++ str
  let n := str.length
  for i in [:n] do
    let j := i + 1
    let substring := (tmp.drop j).take n
    if str == substring then
      return j
  return n

end Task9


-- Tests
#guard Task9.find_Rotations "aaaa" == 1
#guard Task9.find_Rotations "ab" == 2
#guard Task9.find_Rotations "abc" == 3
