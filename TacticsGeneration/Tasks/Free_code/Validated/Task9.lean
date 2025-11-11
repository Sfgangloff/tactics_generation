import Batteries
open Std



/-!
  Auto-generated from task 9.
  Module: Task9
-/

namespace Task9

-- Return the minimum k > 0 such that rotating s by k yields s again.
-- If s is empty, we return 0.
-- Rotation check uses only String.drop, String.take, String.length, and (++) as required.
def findRotations (s : String) : Nat :=
  let n := s.length
  if n == 0 then 0
  else
    let rec loop (k fuel : Nat) : Nat :=
      match fuel with
      | 0 => n
      | fuel' + 1 =>
        if s == (s.drop k) ++ (s.take k) then
          k
        else
          loop (k + 1) fuel'
    loop 1 n

end Task9


-- Tests
#guard Task9.findRotations "aaaa" == 1
#guard Task9.findRotations "ab" == 2
#guard Task9.findRotations "abc" == 3