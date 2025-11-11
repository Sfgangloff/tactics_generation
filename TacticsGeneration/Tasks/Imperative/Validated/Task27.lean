import Batteries



/-!
  Auto-generated from task 27.
  Module: Task27
-/

open Std

namespace Task27

-- Remove all digits from each string in the input array.
-- Mirrors the Python implementation using imperative style.
def remove (xs : Array String) : Array String := Id.run do
  let digit0 : Nat := ('0' : Char).toNat
  let digit9 : Nat := ('9' : Char).toNat
  let mut res : Array String := #[]
  for s in xs do
    let mut t := ""
    for c in s.data do
      let n := c.toNat
      if !(digit0 ≤ n && n ≤ digit9) then
        t := t.push c
    res := res.push t
  return res

end Task27


-- Tests
open Std
open Task27

#guard remove #["4words", "3letters", "4digits"] == #["words", "letters", "digits"]
#guard remove #["28Jan","12Jan","11Jan"] == #["Jan","Jan","Jan"]
#guard remove #["wonder1","wonder2","wonder3"] == #["wonder","wonder","wonder"]
