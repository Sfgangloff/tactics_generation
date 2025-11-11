import Batteries
open Std

def reverseString (s : String) : String :=
  String.mk (s.data.reverse)

def listGetD {α} (xs : List α) (i : Nat) (d : α) : α :=
  match xs.drop i with
  | [] => d
  | x :: _ => x

def countReversePairs (testList : List String) : String := Id.run do
  let n := testList.length
  let mut res := 0
  for i in [0 : n] do
    let ri := reverseString (listGetD testList i "")
    for j in [i : n] do
      if listGetD testList j "" == ri then
        res := res + 1
  return toString res

#guard countReversePairs ["julia", "best", "tseb", "for", "ailuj"] == "2"
#guard countReversePairs ["geeks", "best", "for", "skeeg"] == "1"
#guard countReversePairs ["makes", "best", "sekam", "for", "rof"] == "2"
