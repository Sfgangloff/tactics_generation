import Batteries



/-!
  Auto-generated from task 29.
  Module: Task29
-/

open Std

namespace Task29

/--
  Find the element occurring an odd number of times.
  Precondition: `arr_size ≤ arr.size`.
-/
def getOddOccurrence (arr : Array Int) (arr_size : Nat) : Int :=
  Id.run do
    for i in [:arr_size] do
      let mut count : Nat := 0
      for j in [:arr_size] do
        if arr[i]! == arr[j]! then
          count := count + 1
      if count % 2 == 1 then
        return arr[i]!
    return (-1)

end Task29


-- Tests
open Std

open Task29

#guard getOddOccurrence #[1,2,3,1,2,3,1] 7 == 1
#guard getOddOccurrence #[1,2,3,2,3,1,3] 7 == 3
#guard getOddOccurrence #[2,3,5,4,5,2,4,3,5,2,4,4,2] 13 == 5
