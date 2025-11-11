import Batteries

open Std

def isPalindromeStr (s : String) : Bool :=
  s == String.mk (s.toList.reverse)

def previousPalindrome (num : Nat) : Nat := Id.run do
  if num = 0 then
    return 0
  let mut x := num - 1
  while x > 0 do
    let s := toString x
    if isPalindromeStr s then
      return x
    x := x - 1
  return 0

#guard previousPalindrome 99 = 88
#guard previousPalindrome 1221 = 1111
#guard previousPalindrome 120 = 111
