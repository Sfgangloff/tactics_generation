import Batteries
open Std

/-!
  Auto-generated from task 18.
  Module: Task18
-/

namespace Task18

-- Remove characters from the first string which are present in the second string.
-- Assumes ASCII for counting (0..255). Non-ASCII chars are treated as not present in the second string (kept).
def remove_dirty_chars (string : String) (second_string : String) : String := Id.run do
  -- Build count array of size 256 for characters in second_string
  let mut count : Array Nat := Array.replicate 256 0
  for c in second_string.data do
    let idx := c.toNat
    if idx < 256 then
      let old := count[idx]!
      count := count.set! idx (old + 1)
  -- Convert first string to Array Char to allow indexed in-place style
  let mut strArr : Array Char := #[]
  for c in string.data do
    strArr := strArr.push c
  -- Two-index in-place filtering (like the Python code)
  let mut resIndex : Nat := 0
  for ipIndex in [:strArr.size] do
    let c := strArr[ipIndex]!
    let idx := c.toNat
    let mut keep := true
    if idx < 256 then
      if count[idx]! == 0 then
        keep := true
      else
        keep := false
    if keep then
      strArr := strArr.set! resIndex c
      resIndex := resIndex + 1
  -- Build the resulting string from the first resIndex characters
  let mut resStr : String := ""
  for i in [:resIndex] do
    resStr := resStr.push (strArr[i]!)
  return resStr

end Task18


-- Tests
open Task18

#eval
  let r := remove_dirty_chars "probasscurve" "pros"
  if r == "bacuve" then () else panic! s!"expected 'bacuve', got {r}"

#eval
  let r := remove_dirty_chars "digitalindia" "talent"
  if r == "digiidi" then () else panic! s!"expected 'digiidi', got {r}"

#eval
  let r := remove_dirty_chars "exoticmiles" "toxic"
  if r == "emles" then () else panic! s!"expected 'emles', got {r}"