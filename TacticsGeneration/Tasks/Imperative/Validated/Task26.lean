import Batteries
open Std

/-!
  Auto-generated from task 26.
  Module: Task26
-/

namespace Task26

-- Checks whether every element in every inner array equals K.
-- Preconditions: test_list contains arrays of Nats; indices are assumed valid when accessed.
def check_k_elements (test_list : Array (Array Nat)) (K : Nat) : Bool := Id.run do
  let mut res := true
  for tup in test_list do
    for ele in tup do
      if ele != K then
        res := false
  return res

end Task26


-- Tests
open Task26

#guard check_k_elements (#[#[4,4], #[4,4,4], #[4,4], #[4,4,4,4], #[4]]) 4 = true
#guard check_k_elements (#[#[7,7,7], #[7,7]]) 7 = true
#guard check_k_elements (#[#[9,9], #[9,9,9,9]]) 7 = false

-- Challenge test
#guard check_k_elements (#[#[4,4], #[4,4,4], #[4,4], #[4,4,6,4], #[4]]) 4 = false