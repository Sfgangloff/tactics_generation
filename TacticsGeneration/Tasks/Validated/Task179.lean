import Batteries
open Std

def collectDigits (temp : Nat) (acc : List Nat) (n : Nat) : (List Nat × Nat) :=
  let rec loop (temp : Nat) (acc : List Nat) (n : Nat) (fuel : Nat) : (List Nat × Nat) :=
    match fuel with
    | 0 => (acc, n)
    | fuel' + 1 =>
      if temp > 0 then
        loop (temp / 10) (acc ++ [temp % 10]) (n + 1) fuel'
      else
        (acc, n)
  loop temp acc n (temp + 1)

def keithLoop (x n : Nat) (terms : Array Nat) (i nextTerm : Nat) : Bool :=
  let rec loop (terms : Array Nat) (i nextTerm : Nat) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      if nextTerm < x then
        let s := Id.run do
          let mut s := 0
          for j in [1 : n + 1] do
            let idx := i - j
            let v := Array.getD terms idx 0
            s := s + v
          return s
        loop (terms.push s) (i + 1) s fuel'
      else
        nextTerm == x
  loop terms i nextTerm (x + 10000)

def isNumKeith (x : Nat) : Bool := Id.run do
  let (termsLE, n) := collectDigits x [] 0
  let termsList := termsLE.reverse
  let termsArr : Array Nat := Array.mk termsList
  return keithLoop x n termsArr n 0

#guard isNumKeith 14 == true
#guard isNumKeith 12 == false
#guard isNumKeith 197 == true
