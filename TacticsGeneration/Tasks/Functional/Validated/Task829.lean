import Batteries
open Std

def secondFrequent (input : List String) : String := Id.run do
  
  let rec inc (xs : List (String × Nat)) (k : String) : List (String × Nat) :=
    match xs with
    | [] => [(k, 1)]
    | (k', n) :: t =>
      if k = k' then
        (k', n + 1) :: t
      else
        (k', n) :: inc t k
  let mut m : List (String × Nat) := []
  for s in input do
    m := inc m s
  
  let mut max1 : Nat := 0
  let mut max2 : Nat := 0
  for p in m do
    let c := p.snd
    if c > max1 then
      max2 := max1
      max1 := c
    else if c > max2 then
      max2 := c
  
  for p in m do
    let k := p.fst
    let c := p.snd
    if c == max2 then
      return k
  return ""

#guard secondFrequent ["aaa","bbb","ccc","bbb","aaa","aaa"] = "bbb"
#guard secondFrequent ["abc","bcd","abc","bcd","bcd","bcd"] = "abc"
#guard secondFrequent ["cdma","gsm","hspa","gsm","cdma","cdma"] = "gsm"
