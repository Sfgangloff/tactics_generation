import Batteries

open Std

def armstrong_number (number : Nat) : Bool :=
  let rec countDigits (t : Nat) (acc : Nat) : Nat :=
    if t > 0 then countDigits (t / 10) (acc + 1) else acc
  let times := countDigits number 0
  let rec sumPows (t : Nat) (acc : Nat) : Nat :=
    if t > 0 then
      let reminder := t % 10
      sumPows (t / 10) (acc + reminder ^ times)
    else
      acc
  let s := sumPows number 0
  number == s

#guard armstrong_number 153 == true
#guard armstrong_number 259 == false
#guard armstrong_number 4458 == false
