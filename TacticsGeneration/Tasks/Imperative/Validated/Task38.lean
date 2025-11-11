import Batteries



/-!
  Auto-generated from task 38.
  Module: Task38
-/

open Std

namespace Task38

-- Find the division of the first even and first odd number in the given array.
-- If either is not found, defaults remain -1 as in the Python version.
-- Preconditions: the array is assumed to contain at least one odd number to avoid division by -1 in tests.
def div_even_odd (list1 : Array Int) : Int := Id.run do
  let mut firstEven : Int := -1
  let mut firstOdd : Int := -1
  for el in list1 do
    if firstEven == -1 && el % 2 == 0 then
      firstEven := el
    if firstOdd == -1 && el % 2 != 0 then
      firstOdd := el
    if firstEven != -1 && firstOdd != -1 then
      return firstEven / firstOdd
  return firstEven / firstOdd

end Task38


-- Tests
open Std
open Task38

#guard div_even_odd #[1,3,5,7,4,1,6,8] == 4
#guard div_even_odd #[1,2,3,4,5,6,7,8,9,10] == 2
#guard div_even_odd #[1,5,7,9,10] == 10
