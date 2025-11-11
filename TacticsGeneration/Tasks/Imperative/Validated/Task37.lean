import Batteries
open Std

/-!
  Auto-generated from task 37.
  Module: Task37
-/

/-
We represent the mixed Python list (ints and strings) as Array (Sum Nat String),
where Sum.inl n is an integer and Sum.inr s is a string.
-/

def selectionSortNat (arr : Array Nat) : Array Nat := Id.run do
  let mut a := arr
  let n := a.size
  for i in [:n] do
    let mut minIdx := i
    let mut minVal := a[i]!
    for j in [i+1:n] do
      let v := a[j]!
      if v < minVal then
        minVal := v
        minIdx := j
    let vi := a[i]!
    a := a.set! i minVal
    a := a.set! minIdx vi
  return a

def selectionSortString (arr : Array String) : Array String := Id.run do
  let mut a := arr
  let n := a.size
  for i in [:n] do
    let mut minIdx := i
    let mut minVal := a[i]!
    for j in [i+1:n] do
      let v := a[j]!
      if v < minVal then
        minVal := v
        minIdx := j
    let vi := a[i]!
    a := a.set! i minVal
    a := a.set! minIdx vi
  return a

def sort_mixed_list (mixed_list : Array (Sum Nat String)) : Array (Sum Nat String) := Id.run do
  -- Separate ints and strings
  let mut ints : Array Nat := #[]
  let mut strs : Array String := #[]
  for x in mixed_list do
    match x with
    | Sum.inl n => ints := ints.push n
    | Sum.inr s => strs := strs.push s
  -- Sort both parts using imperative selection sort
  let intsSorted := selectionSortNat ints
  let strsSorted := selectionSortString strs
  -- Concatenate: ints first, then strings
  let mut res : Array (Sum Nat String) := #[]
  for n in intsSorted do
    res := res.push (Sum.inl n)
  for s in strsSorted do
    res := res.push (Sum.inr s)
  return res


-- Tests

-- Test 1
#guard
  let input : Array (Sum Nat String) := #[
    .inl 19, .inr "red", .inl 12, .inr "green", .inr "blue", .inl 10, .inr "white", .inr "green", .inl 1
  ]
  let expected : Array (Sum Nat String) := #[
    .inl 1, .inl 10, .inl 12, .inl 19, .inr "blue", .inr "green", .inr "green", .inr "red", .inr "white"
  ]
  sort_mixed_list input = expected

-- Test 2 (same as Python repeated assert)
#guard
  let input : Array (Sum Nat String) := #[
    .inl 19, .inr "red", .inl 12, .inr "green", .inr "blue", .inl 10, .inr "white", .inr "green", .inl 1
  ]
  let expected : Array (Sum Nat String) := #[
    .inl 1, .inl 10, .inl 12, .inl 19, .inr "blue", .inr "green", .inr "green", .inr "red", .inr "white"
  ]
  sort_mixed_list input = expected

-- Test 3 (same again)
#guard
  let input : Array (Sum Nat String) := #[
    .inl 19, .inr "red", .inl 12, .inr "green", .inr "blue", .inl 10, .inr "white", .inr "green", .inl 1
  ]
  let expected : Array (Sum Nat String) := #[
    .inl 1, .inl 10, .inl 12, .inl 19, .inr "blue", .inr "green", .inr "green", .inr "red", .inr "white"
  ]
  sort_mixed_list input = expected