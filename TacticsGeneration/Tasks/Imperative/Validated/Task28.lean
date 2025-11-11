import Batteries



/-!
  Auto-generated from task 28.
  Module: Task28
-/

open Std

namespace Task28

-- Computes the binomial coefficient C(n, k) in imperative style (no recursion)
-- Preconditions: n, k are natural numbers
-- Uses the iterative identity: C(n, i) = C(n, i-1) * (n - i + 1) / i
def binomial_Coeff (n k : Nat) : Nat := Id.run do
  if k > n then
    return 0
  if k == 0 || k == n then
    return 1
  let mut kk := k
  if kk > n - kk then
    kk := n - kk
  let mut res : Nat := 1
  let mut i : Nat := 0
  -- Loop kk times; at step i, res becomes C(n, i)
  for _ in [:kk] do
    res := res * (n - i)
    res := res / (i + 1)
    i := i + 1
  return res

end Task28


-- Tests
open Std
open Task28

#guard binomial_Coeff 5 2 == 10
#guard binomial_Coeff 4 3 == 4
#guard binomial_Coeff 3 2 == 3
#guard binomial_Coeff 14 6 == 3003
