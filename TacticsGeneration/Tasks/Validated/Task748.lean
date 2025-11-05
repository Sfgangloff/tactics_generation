import Batteries

open Std

def isBetween (c lo hi : Char) : Bool := (lo ≤ c) && (c ≤ hi)

def isWordChar (c : Char) : Bool :=
  isBetween c 'a' 'z' || isBetween c 'A' 'Z' || isBetween c '0' '9' || (c == '_')

def isUpperAZ (c : Char) : Bool := isBetween c 'A' 'Z'

def capitalWordsSpaces (str1 : String) : String :=
  let chars := str1.data
  let (_, acc) := chars.foldl (init := (false, ([] : List Char))) (fun (st : Bool × List Char) (c : Char) =>
    let prevIsWord := st.fst
    let acc := st.snd
    let acc' := if prevIsWord && isUpperAZ c then c :: ' ' :: acc else c :: acc
    (isWordChar c, acc')
  )
  String.mk acc.reverse

#guard capitalWordsSpaces "Python" = "Python"
#guard capitalWordsSpaces "PythonProgrammingExamples" = "Python Programming Examples"
#guard capitalWordsSpaces "GetReadyToBeCodingFreak" = "Get Ready To Be Coding Freak"
