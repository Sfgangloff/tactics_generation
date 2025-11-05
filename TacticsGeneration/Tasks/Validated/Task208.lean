import Batteries

open Std

def isDigit (c : Char) : Bool := ('0' ≤ c) && (c ≤ '9')

partial def consumeDigits : List Char → Nat → (Nat × List Char)
  | [], acc => (acc, [])
  | c :: cs, acc => if isDigit c then consumeDigits cs (acc + 1) else (acc, c :: cs)

def isDecimal (num : String) : Bool :=
  let cs := num.data
  let (n1, rest) := consumeDigits cs 0
  if n1 == 0 then false else
    match rest with
    | [] => true
    | c :: rest2 =>
      if c == '.' then
        let (n2, rest3) := consumeDigits rest2 0
        (n2 == 1 || n2 == 2) && rest3.isEmpty
      else
        false

#guard isDecimal "123.11" == true
#guard isDecimal "0.21" == true
#guard isDecimal "123.1214" == false
