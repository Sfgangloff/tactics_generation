import Batteries
open Std

namespace Task25

/--
Precondition: `n ≤ arr.size`. Mirrors Python behavior of multiplying each distinct element once.
We avoid sorting (per constraints) and use a HashSet to track seen elements.
-/
def find_Product (arr : Array Nat) (n : Nat) : Nat := Id.run do
  let mut seen : Std.HashSet Nat := Std.HashSet.emptyWithCapacity n
  let mut prod : Nat := 1
  for i in [:n] do
    let x := arr[i]!
    if seen.contains x then
      ()
    else
      seen := seen.insert x
      prod := prod * x
  return prod

end Task25


-- Tests
open Task25

#eval (
  let r := find_Product #[1,1,2,3] 4
  if r == 6 then () else panic! "assert failed: find_Product([1,1,2,3],4) == 6"
)

#eval (
  let r := find_Product #[1,2,3,1,1] 5
  if r == 6 then () else panic! "assert failed: find_Product([1,2,3,1,1],5) == 6"
)

#eval (
  let r := find_Product #[1,1,4,5,6] 5
  if r == 120 then () else panic! "assert failed: find_Product([1,1,4,5,6],5) == 120"
)

#eval (
  let r := find_Product #[1,1,4,5,6,5,7,1,1,3,4] 11
  if r == 2520 then () else panic! "assert failed: challenge test == 2520"
)