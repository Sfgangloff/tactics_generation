import Batteries

open Std

private def isLowerASCII (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'
private def isUpperASCII (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'
private def isDigitASCII (c : Char) : Bool := '0' ≤ c && c ≤ '9'
private def asciiLower (c : Char) : Char := if isUpperASCII c then Char.ofNat (c.toNat + 32) else c

def camel_to_snake (text : String) : String :=
  let chars : List Char := text.data
  let rec go (prev? : Option Char) (cs : List Char) : List Char :=
    match cs with
    | [] => []
    | c :: t =>
      let needsUnderscore :=
        match prev? with
        | none => false
        | some prev =>
          let nextLower := match t with | d :: _ => isLowerASCII d | [] => false
          isUpperASCII c && (isLowerASCII prev || isDigitASCII prev || nextLower)
      if needsUnderscore then
        '_' :: c :: go (some c) t
      else
        c :: go (some c) t
  let lst := go none chars
  String.mk (lst.map asciiLower)

#guard camel_to_snake "PythonProgram" == "python_program"
#guard camel_to_snake "pythonLanguage" == "python_language"
#guard camel_to_snake "ProgrammingLanguage" == "programming_language"
