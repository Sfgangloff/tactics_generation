import Batteries



/-!
  Auto-generated from task 30.
  Module: Task30
-/

open Std

namespace Task30

-- Precondition: input string is non-empty when this function is called
-- (in our usage below, we only call it on substrings of length ≥ 1)
def check_Equality (s : String) : Bool := Id.run do
  let arr : Array Char := s.data.toArray
  let first := arr[0]!
  let last := arr[arr.size - 1]!
  return first == last

def count_Substring_With_Equal_Ends (s : String) : Nat := Id.run do
  let n := s.length
  let mut result := 0
  for i in [:n] do
    let maxj := n - i
    for k in [:maxj] do
      let j := k + 1
      let sub := (s.drop i).take j
      if check_Equality sub then
        result := result + 1
  return result

end Task30


-- Tests
open Std
open Task30

#eval
  if count_Substring_With_Equal_Ends "abc" == 3 then
    0
  else
    panic! "Test 1 failed"

#eval
  if count_Substring_With_Equal_Ends "abcda" == 6 then
    0
  else
    panic! "Test 2 failed"

#eval
  if count_Substring_With_Equal_Ends "ab" == 2 then
    0
  else
    panic! "Test 3 failed"
