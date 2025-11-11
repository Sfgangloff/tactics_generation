import Batteries

open Std

def isAsciiDigit (c : Char) : Bool :=
  let n := c.toNat
  let n0 := ('0' : Char).toNat
  let n9 := ('9' : Char).toNat
  n0 ≤ n && n ≤ n9

partial def takeDigits (xs : List Char) : Nat × List Char :=
  match xs with
  | [] => (0, [])
  | c :: cs =>
    if isAsciiDigit c then
      let (k, rest) := takeDigits cs
      (k + 1, rest)
    else
      (0, xs)

def isDecimal (num : String) : Bool :=
  let chars := num.data
  let (k, rest) := takeDigits chars
  if k == 0 then false else
    match rest with
    | [] => true
    | c :: rem =>
      if c == '.' then
        let (k2, rem2) := takeDigits rem
        ((k2 == 1) || (k2 == 2)) && rem2.isEmpty
      else
        false

#guard isDecimal "123.11" == true
#guard isDecimal "e666.86" == false
#guard isDecimal "3.124587" == false
