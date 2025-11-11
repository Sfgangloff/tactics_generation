import Batteries

open Std

def isValidParenthese (str1 : String) : Bool :=
  let final := str1.foldl (init := (some ([] : List Char))) (fun acc c =>
    match acc with
    | none => none
    | some stack =>
      if c == '(' || c == '{' || c == '[' then
        some (c :: stack)
      else
        match stack with
        | [] => none
        | top :: rest =>
          match top with
          | '(' => if c == ')' then some rest else none
          | '{' => if c == '}' then some rest else none
          | '[' => if c == ']' then some rest else none
          | _ => none
  )
  match final with
  | some [] => true
  | _ => false

#guard isValidParenthese "(){}[]" == true
#guard isValidParenthese "()[{)}" == false
#guard isValidParenthese "()" == true
