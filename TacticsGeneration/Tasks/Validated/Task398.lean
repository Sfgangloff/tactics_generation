import Batteries

open Std

def sumOfDigits {α} [ToString α] (nums : List α) : Nat :=
  nums.foldl (fun acc n =>
    (toString n).toList.foldl (fun acc2 c =>
      if c.isDigit then acc2 + (c.toNat - '0'.toNat) else acc2
    ) acc
  ) 0

#guard sumOfDigits ([10, 2, 56] : List Int) = 14
#guard sumOfDigits ["[10,20,4,5,'b',70,'a']"] = 19
#guard sumOfDigits ([10, 20, -4, 5, -70] : List Int) = 19
