import Batteries
open Std

def nextSmallestPalindrome (num : Nat) : Nat :=
  let isPalindrome (n : Nat) : Bool :=
    let s := toString n
    s == String.mk s.data.reverse
  let rec findNext (n : Nat) (limit : Nat) : Nat :=
    if h : limit > 0 then
      if isPalindrome n then n else findNext (n + 1) (limit - 1)
    else
      n
  findNext (num + 1) 1_000_000

#eval nextSmallestPalindrome 99 == 101
#eval nextSmallestPalindrome 1221 == 1331
#eval nextSmallestPalindrome 120 == 121
