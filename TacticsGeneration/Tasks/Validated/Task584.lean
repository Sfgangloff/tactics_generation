import Batteries
open Std

def isWordChar (c : Char) : Bool :=
  let n := c.toNat
  let isLower := ('a'.toNat ≤ n) && (n ≤ 'z'.toNat)
  let isUpper := ('A'.toNat ≤ n) && (n ≤ 'Z'.toNat)
  let isDigit := ('0'.toNat ≤ n) && (n ≤ '9'.toNat)
  isLower || isUpper || isDigit || (n == '_'.toNat)

def listNth? {α} (xs : List α) (i : Nat) : Option α :=
  match xs, i with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs', i+1 => listNth? xs' i

def charAt? (s : String) (i : Nat) : Option Char :=
  listNth? s.data i

def advanceWord (s : String) (j : Nat) (_n : Nat) : Nat :=
  let tail := s.drop j
  let rec count (cs : List Char) (acc : Nat) : Nat :=
    match cs with
    | [] => acc
    | c :: cs' =>
      if isWordChar c then count cs' (acc + 1) else acc
  j + count tail.data 0

def findAdverbs (text : String) : String := Id.run do
  let n := text.length
  let mut res : Option String := none
  let mut stop : Bool := false
  for i in [0 : n] do
    if !stop then
      match charAt? text i with
      | some c =>
        if isWordChar c then
          let prevWord :=
            if i == 0 then false
            else
              match charAt? text (i - 1) with
              | some pc => isWordChar pc
              | none => false
          if !prevWord then
            let j := advanceWord text i n
            let tokLen := j - i
            if tokLen >= 3 then
              let token := (text.drop i).take tokLen
              if token.length >= 2 && token.drop (token.length - 2) == "ly" then
                let r := toString i ++ "-" ++ toString j ++ ": " ++ token
                res := some r
                stop := true
            else
              pure ()
          else
            pure ()
        else
          pure ()
      | none => pure ()
    else
      pure ()
  return res.getD ""

#guard findAdverbs "Clearly, he has no excuse for such behavior." == "0-7: Clearly"
#guard findAdverbs "Please handle the situation carefuly" == "28-36: carefuly"
#guard findAdverbs "Complete the task quickly" == "18-25: quickly"
