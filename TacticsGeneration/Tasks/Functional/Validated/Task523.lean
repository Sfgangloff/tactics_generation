import Batteries

open Std

inductive BoolOrString
| bool (b : Bool)
| str (s : String)

deriving Repr, BEq

def isUpperAscii (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'
def isLowerAscii (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'
def isDigitAscii (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def checkString (str1 : String) : List String :=
  let messg : List (String → BoolOrString) := [
    (fun s => if s.toList.any isUpperAscii then BoolOrString.bool true else BoolOrString.str "String must have 1 upper case character."),
    (fun s => if s.toList.any isLowerAscii then BoolOrString.bool true else BoolOrString.str "String must have 1 lower case character."),
    (fun s => if s.toList.any isDigitAscii then BoolOrString.bool true else BoolOrString.str "String must have 1 number."),
    (fun s => if s.length ≥ 7 then BoolOrString.bool true else BoolOrString.str "String length should be atleast 8.")
  ]
  let rs := messg.map (fun f => f str1)
  let result := rs.foldl (fun acc r =>
    match r with
    | BoolOrString.bool _ => acc
    | BoolOrString.str s => acc ++ [s]
  ) []
  if result.isEmpty then ["Valid string."] else result

#guard checkString "python" = ["String must have 1 upper case character.", "String must have 1 number.", "String length should be atleast 8."]
#guard checkString "123python" = ["String must have 1 upper case character."]
#guard checkString "123Python" = ["Valid string."]
