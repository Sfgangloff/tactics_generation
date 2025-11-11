import Batteries



/-!
  Auto-generated from task 15.
  Module: Task15
-/

open Std

/-- Return true iff the character is an ASCII lowercase letter 'a'..'z'. -/
def isLowerAscii (c : Char) : Bool :=
  match c with
  | 'a' | 'b' | 'c' | 'd' | 'e' | 'f' | 'g' | 'h' | 'i' | 'j' | 'k' | 'l' | 'm'
  | 'n' | 'o' | 'p' | 'q' | 'r' | 's' | 't' | 'u' | 'v' | 'w' | 'x' | 'y' | 'z' => true
  | _ => false

/-- Collect character indices (0-based, by characters) where the string has lowercase letters. -/
def lowerStarts (s : String) : List Nat :=
  let rec go (cs : List Char) (i : Nat) (acc : List Nat) : List Nat :=
    match cs with
    | [] => acc.reverse
    | c :: cs' =>
      if isLowerAscii c then
        go cs' (i+1) (i :: acc)
      else
        go cs' (i+1) acc
  go s.data 0 []

/-- Build segments starting at each index in `starts`, ending just before the next such index or at the end. -/
def buildSegments (s : String) (starts : List Nat) : List String :=
  let rec go (st : List Nat) (acc : List String) : List String :=
    match st with
    | [] => acc.reverse
    | [i] => ((s.drop i) :: acc).reverse
    | i :: j :: rest =>
      let seg := (s.drop i).take (j - i)
      go (j :: rest) (seg :: acc)
  go starts []

/-- Split a string at lowercase letters: for each lowercase letter position i, take the substring from i up to (but not including) the next lowercase position, or to the end if none. -/
def splitLowerString (s : String) : List String :=
  buildSegments s (lowerStarts s)


-- Tests
#guard splitLowerString "AbCd" == ["bC", "d"]
#guard splitLowerString "Python" == ["y", "t", "h", "o", "n"]
#guard splitLowerString "Programming" == ["r", "o", "g", "r", "a", "m", "m", "i", "n", "g"]
