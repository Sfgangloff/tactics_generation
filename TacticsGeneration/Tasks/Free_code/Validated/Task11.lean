import Batteries
open Std

/-!
  Auto-generated from task 11.
  Module: Task11
-/

namespace Task11

-- Remove the first and last occurrence of substring c (assumed non-empty, typically a single character)
-- from the string s. If c does not occur or occurs once, the function removes those occurrences
-- accordingly.
def removeOcc (s : String) (c : String) : String :=
  let parts := s.splitOn c
  match parts with
  | [] => s
  | [_] => s
  | a :: b :: rest =>
      let rec go (xs : List String) (acc : String) : String :=
        match xs with
        | [] => acc
        | [last] => acc ++ last
        | h :: t => go t (acc ++ c ++ h)
      go rest (a ++ b)

end Task11


-- Tests
#guard Task11.removeOcc "hello" "l" == "heo"
#guard Task11.removeOcc "abcda" "a" == "bcd"
#guard Task11.removeOcc "PHP" "P" == "H"

-- Challenge tests
#guard Task11.removeOcc "hellolloll" "l" == "helollol"
#guard Task11.removeOcc "" "l" == ""