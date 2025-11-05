import Batteries

open Std

partial def consumeAfterOpen (rest : List Char) : Option (List Char) :=
  match rest with
  | [] => none
  | ')' :: _ => none
  | _ =>
    let rec find (cs : List Char) : Option (List Char) :=
      match cs with
      | [] => none
      | ')' :: after => some after
      | _ :: t => find t
    find rest

partial def removeParenAreaAux (acc : List Char) (cs : List Char) : List Char :=
  match cs with
  | [] => acc.reverse
  | '(' :: rest =>
      match consumeAfterOpen rest with
      | some after =>
          let acc' := match acc with
            | ' ' :: accTail => accTail
            | _ => acc
          removeParenAreaAux acc' after
      | none =>
          removeParenAreaAux ('(' :: acc) rest
  | c :: rest => removeParenAreaAux (c :: acc) rest

def removeParenArea (s : String) : String :=
  String.mk (removeParenAreaAux [] s.toList)

def removeParenthesis (items : List String) : String :=
  
  match items with
  | item :: _ => removeParenArea item
  | [] => ""

#guard removeParenthesis ["python (chrome)"] = "python"
#guard removeParenthesis ["string(.abc)"] = "string"
#guard removeParenthesis ["alpha(num)"] = "alpha"
