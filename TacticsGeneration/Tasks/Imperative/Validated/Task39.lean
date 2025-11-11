import Batteries



/-!
  Auto-generated from task 39.
  Module: Task39
-/

open Std

namespace Task39

-- Preconditions: We treat String as sequence of Chars; indices assumed valid when used.
-- Returns a rearranged string where no adjacent chars are equal, or "" if impossible.
def rearange_string (S : String) : String := Id.run do
  -- Build frequency counts as an Array of (Char × Nat)
  let mut counts : Array (Char × Nat) := #[]
  for c in S.data do
    let mut found := false
    let mut idx := 0
    for j in [:counts.size] do
      if (counts[j]!).fst == c then
        found := true
        idx := j
        break
    if found then
      let (ch, n) := counts[idx]!
      counts := counts.set! idx (ch, n + 1)
    else
      counts := counts.push (c, 1)

  -- Compute maximum count
  let mut maxCount : Nat := 0
  for p in counts do
    if p.snd > maxCount then
      maxCount := p.snd

  let n := S.length
  -- Feasibility check
  if maxCount * 2 > n + 1 then
    return ""

  -- Greedy construction by repeatedly taking the two highest counts (lexicographically tie-broken)
  let mut ans : Array Char := #[]
  for _ in [:n] do
    -- pick top1
    let mut have1 := false
    let mut top1Idx : Nat := 0
    let mut top1Cnt : Nat := 0
    let mut top1Ch  : Char := '\u0000'
    for j in [:counts.size] do
      let (ch, cnt) := counts[j]!
      if cnt > 0 then
        if !have1 then
          have1 := true
          top1Idx := j; top1Cnt := cnt; top1Ch := ch
        else
          if cnt > top1Cnt then
            top1Idx := j; top1Cnt := cnt; top1Ch := ch
          else
            if cnt == top1Cnt then
              if ch < top1Ch then
                top1Idx := j; top1Ch := ch
    if !have1 then
      break

    -- pick top2 (excluding top1), with same tie-breaking
    let mut have2 := false
    let mut top2Idx : Nat := 0
    let mut top2Cnt : Nat := 0
    let mut top2Ch  : Char := '\u0000'
    for j in [:counts.size] do
      if j == top1Idx then
        continue
      let (ch, cnt) := counts[j]!
      if cnt > 0 then
        if !have2 then
          have2 := true
          top2Idx := j; top2Cnt := cnt; top2Ch := ch
        else
          if cnt > top2Cnt then
            top2Idx := j; top2Cnt := cnt; top2Ch := ch
          else
            if cnt == top2Cnt then
              if ch < top2Ch then
                top2Idx := j; top2Ch := ch
    if !have2 then
      break

    -- append both
    ans := ans.push top1Ch
    ans := ans.push top2Ch

    -- decrement their counts
    let (ch1, c1) := counts[top1Idx]!
    counts := counts.set! top1Idx (ch1, c1 - 1)
    let (ch2, c2) := counts[top2Idx]!
    counts := counts.set! top2Idx (ch2, c2 - 1)

  -- Append any leftover single character if present
  let mut leftover : Option Char := none
  for j in [:counts.size] do
    let (ch, cnt) := counts[j]!
    if cnt > 0 then
      leftover := some ch
      break
  match leftover with
  | some ch =>
    ans := ans.push ch
  | none => ()

  return String.mk ans.toList

end Task39


-- Tests
open Std

open Task39

#guard rearange_string "aab" = "aba"
#guard rearange_string "aabb" = "abab"
#guard rearange_string "abccdd" = "cdabcd"
