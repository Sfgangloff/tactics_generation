import Batteries

open Std

def isUpperAscii (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'

def isLowerAscii (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'

def isDigitAscii (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def toLowerAscii (c : Char) : Char := if isUpperAscii c then Char.ofNat (c.toNat + 32) else c

def camelToSnake (text : String) : String :=
  let chars := text.data
  let rec loop (prev? : Option Char) (cs : List Char) (acc : List Char) : List Char :=
    match cs with
    | [] => acc
    | c :: rest =>
      let next? : Option Char := match rest with | [] => none | n :: _ => some n
      let hasPrev := match prev? with | some _ => true | none => false
      let nextIsLower := match next? with | some n => isLowerAscii n | none => false
      let prevIsLowerOrDigit := match prev? with | some p => isLowerAscii p || isDigitAscii p | none => false
      let needUnderscore := isUpperAscii c && hasPrev && (nextIsLower || prevIsLowerOrDigit)
      let acc := if needUnderscore then '_' :: acc else acc
      let acc := toLowerAscii c :: acc
      loop (some c) rest acc
  String.mk <| (loop none chars []).reverse

#guard camelToSnake "GoogleAssistant" == "google_assistant"
#guard camelToSnake "ChromeCast" == "chrome_cast"
#guard camelToSnake "QuadCore" == "quad_core"
