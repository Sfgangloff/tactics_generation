import Batteries



/-!
  Auto-generated from task 7.
  Module: Task7
-/

open Std

namespace Task7

-- Find all words with length >= 4, where a word is [A-Za-z0-9_]+ (regex-like \w)
-- Mirrors regex: /\b\w{4,}\b/
def findCharLong (text : String) : Array String := Id.run do
  let mut res : Array String := #[]
  let mut cur : String := ""
  -- helper: ASCII word char predicate (A-Z, a-z, 0-9, _)
  let isWordChar := fun (c : Char) =>
    let n := c.toNat
    (n >= 48 && n <= 57) || (n >= 65 && n <= 90) || (n >= 97 && n <= 122) || c == '_'
  for c in text.data do
    if isWordChar c then
      cur := cur.push c
    else
      if cur.length >= 4 then
        res := res.push cur
      cur := ""
  -- flush tail
  if cur.length >= 4 then
    res := res.push cur
  return res

end Task7


-- Tests
open Std

-- Tests mirroring the Python asserts
#eval (Task7.findCharLong "Please move back to stream") == #["Please", "move", "back", "stream"]
#eval (Task7.findCharLong "Jing Eco and Tech") == #["Jing", "Tech"]
#eval (Task7.findCharLong "Jhingai wulu road Zone 3") == #["Jhingai", "wulu", "road", "Zone"]
