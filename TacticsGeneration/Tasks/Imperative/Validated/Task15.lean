import Batteries



/-!
  Auto-generated from task 15.
  Module: Task15
-/

open Std

namespace Task15

-- Split a string at lowercase letters: find groups matching /[a-z][^a-z]*/
-- ASCII lowercase check only, to mirror the Python regex [a-z].
def splitLowerstring (text : String) : Array String := Id.run do
  let mut res : Array String := #[]
  -- Convert String to Array Char for indexed access
  let mut chars : Array Char := #[]
  for c in text.data do
    chars := chars.push c
  let n := chars.size
  let mut i : Nat := 0
  -- Simulate a while loop using a for with manual index and breaks
  for _ in [:n+1] do
    if i >= n then break
    let c := chars[i]!
    let isLower := (Char.toNat c >= Char.toNat 'a') && (Char.toNat c <= Char.toNat 'z')
    if !isLower then
      i := i + 1
      continue
    -- Start of a token at a lowercase letter
    let mut tokenChars : Array Char := #[]
    tokenChars := tokenChars.push c
    i := i + 1
    -- Collect following non-lowercase chars
    for _ in [:n+1] do
      if i >= n then break
      let c2 := chars[i]!
      let isLower2 := (Char.toNat c2 >= Char.toNat 'a') && (Char.toNat c2 <= Char.toNat 'z')
      if isLower2 then break
      tokenChars := tokenChars.push c2
      i := i + 1
    -- Build String from tokenChars
    let mut tokenStr : String := ""
    for ch in tokenChars do
      tokenStr := tokenStr.push ch
    res := res.push tokenStr
  return res

end Task15


-- Tests
open Std
open Task15

#guard (splitLowerstring "AbCd" == #["bC", "d"])
#guard (splitLowerstring "Python" == #["y", "t", "h", "o", "n"])
#guard (splitLowerstring "Programming" == #["r", "o", "g", "r", "a", "m", "m", "i", "n", "g"])
