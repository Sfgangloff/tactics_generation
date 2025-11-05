import Batteries
open Std

def isVowel (c : Char) : Bool :=
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'

def listNth? {α} (xs : List α) (n : Nat) : Option α :=
  let rec go (n : Nat) (xs : List α) : Option α :=
    match n, xs with
    | 0, x :: _ => some x
    | Nat.succ n', _ :: xs' => go n' xs'
    | _, [] => none
  go n xs

def countVowels (testStr : String) : Nat := Id.run do
  let chars := testStr.data
  let len := chars.length
  let mut res := 0
  if len >= 2 then
    
    for idx in [1 : len - 1] do
      let ci := (listNth? chars idx).getD 'a'
      let prev := (listNth? chars (idx - 1)).getD 'a'
      let next := (listNth? chars (idx + 1)).getD 'a'
      if (!isVowel ci) && (isVowel prev || isVowel next) then
        res := res + 1
    
    if (!isVowel ((listNth? chars 0).getD 'a')) && isVowel ((listNth? chars 1).getD 'a') then
      res := res + 1
    
    if (!isVowel ((listNth? chars (len - 1)).getD 'a')) && isVowel ((listNth? chars (len - 2)).getD 'a') then
      res := res + 1
  return res

#guard countVowels "bestinstareels" = 7
#guard countVowels "partofthejourneyistheend" = 12
#guard countVowels "amazonprime" = 5
