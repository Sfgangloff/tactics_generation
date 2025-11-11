import Batteries
open Std

def natLe (a b : Nat) : Bool :=
  match compare a b with
  | Ordering.lt => true
  | Ordering.eq => true
  | Ordering.gt => false

def betweenInclusive (n lo hi : Nat) : Bool := natLe lo n && natLe n hi

def isLowerAZ (c : Char) : Bool :=
  let n := c.toNat
  betweenInclusive n ('a'.toNat) ('z'.toNat)

def isUpperAZ (c : Char) : Bool :=
  let n := c.toNat
  betweenInclusive n ('A'.toNat) ('Z'.toNat)

def isDigit (c : Char) : Bool :=
  let n := c.toNat
  betweenInclusive n ('0'.toNat) ('9'.toNat)

def isWordChar (c : Char) : Bool :=
  isLowerAZ c || isUpperAZ c || isDigit c || c == '_'

def isLowerOrDigit (c : Char) : Bool := isLowerAZ c || isDigit c

def dropWhile (p : Char → Bool) : List Char → List Char
| [] => []
| c :: cs => if p c then dropWhile p cs else (c :: cs)

def consumePlus (p : Char → Bool) (cs : List Char) : Option (List Char) :=
  match cs with
  | [] => none
  | c :: rest => if p c then some (dropWhile p rest) else none

def takeExactlyN (p : Char → Bool) : Nat → List Char → Option (List Char)
| 0, cs => some cs
| Nat.succ _, [] => none
| Nat.succ n, c :: rest => if p c then takeExactlyN p n rest else none

def checkEmail (email : String) : String := Id.run do
  let cs0 := email.data
  
  let some cs1 := consumePlus isLowerOrDigit cs0 | return "Invalid Email"
  
  let cs2 := match cs1 with
    | c :: rest => if (c == '.' || c == '_') then rest else cs1
    | [] => cs1
  
  let some cs3 := consumePlus isLowerOrDigit cs2 | return "Invalid Email"
  
  let cs4opt := match cs3 with
    | '@' :: rest => some rest
    | _ => none
  let some cs4 := cs4opt | return "Invalid Email"
  
  let some cs5 := consumePlus isWordChar cs4 | return "Invalid Email"
  
  let cs6opt := match cs5 with
    | '.' :: rest => some rest
    | _ => none
  let some cs6 := cs6opt | return "Invalid Email"
  
  let ok :=
    match takeExactlyN isWordChar 3 cs6 with
    | some rest => rest.isEmpty
    | none =>
      match takeExactlyN isWordChar 2 cs6 with
      | some rest2 => rest2.isEmpty
      | none => false
  return if ok then "Valid Email" else "Invalid Email"

#guard checkEmail "ankitrai326@gmail.com" == "Valid Email"
#guard checkEmail "my.ownsite@ourearth.org" == "Valid Email"
#guard checkEmail "ankitaoie326.com" == "Invalid Email"
