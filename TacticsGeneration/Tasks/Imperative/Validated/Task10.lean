import Batteries
open Std



/-!
  Auto-generated from task 10.
  Module: Task10
-/


namespace Task10

-- Get the n smallest items from the dataset, in ascending order.
-- Preconditions: none; if n > list1.size, returns all elements sorted ascending.
def small_nnum (list1 : Array Nat) (n : Nat) : Array Nat := Id.run do
  let mut remaining := list1
  let mut result : Array Nat := #[]
  for _ in [:n] do
    if remaining.isEmpty then
      break
    -- remaining is non-empty here
    let mut minVal := remaining[0]!
    let mut minIdx := 0
    for i in [:remaining.size] do
      if remaining[i]! < minVal then
        minVal := remaining[i]!
        minIdx := i
    result := result.push minVal
    let left := remaining.extract 0 minIdx
    let right := remaining.extract (minIdx + 1) remaining.size
    remaining := left ++ right
  return result

end Task10


-- Tests
open Task10

#guard small_nnum (#[10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100]) 2 == #[(10:Nat), 20]
#guard small_nnum (#[10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100]) 5 == #[(10:Nat), 20, 20, 40, 50]
#guard small_nnum (#[10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100]) 3 == #[(10:Nat), 20, 20]