import Batteries
open Std

def isUpperAscii (c : Char) : Bool :=
  let cn := c.toNat
  (Nat.ble (Char.toNat 'A') cn) && (Nat.ble cn (Char.toNat 'Z'))

def takeNonUpper (ds : List Char) (bufRev : List Char) : (List Char × List Char) :=
  match ds with
  | [] => (bufRev.reverse, [])
  | d :: ds' =>
    if isUpperAscii d then
      (bufRev.reverse, d :: ds')
    else
      takeNonUpper ds' (d :: bufRev)

def loopSplitAux (cs : List Char) (accRev : List String) (fuel : Nat) : List String :=
  match fuel with
  | 0 => accRev.reverse
  | Nat.succ fuel' =>
    match cs with
    | [] => accRev.reverse
    | c :: cs' =>
      if isUpperAscii c then
        let (nonUpper, rest) := takeNonUpper cs' []
        let pieceChars := c :: nonUpper
        let piece := String.mk pieceChars
        loopSplitAux rest (piece :: accRev) fuel'
      else
        loopSplitAux cs' accRev fuel'

def splitUpperstring (text : String) : List String :=
  loopSplitAux text.data [] text.length

#guard splitUpperstring "PythonProgramLanguage" == ["Python", "Program", "Language"]
#guard splitUpperstring "PythonProgram" == ["Python", "Program"]
#guard splitUpperstring "ProgrammingLanguage" == ["Programming", "Language"]
