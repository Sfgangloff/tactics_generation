import Batteries
open Std

def MAX : Nat := 1000

private def dropFrontSpaces (cs : List Char) : List Char :=
  match cs with
  | [] => []
  | c :: t => if c == ' ' then dropFrontSpaces t else cs

private def rstripSpaces (cs : List Char) : List Char :=
  let rec trimRev (rev : List Char) : List Char :=
    match rev with
    | [] => []
    | c :: t => if c == ' ' then trimRev t else rev
  (trimRev cs.reverse).reverse

private def trimSpaces (s : String) : String :=
  let cs := s.data
  let cs1 := dropFrontSpaces cs
  let cs2 := rstripSpaces cs1
  String.mk cs2

def replaceSpaces (string : String) : String :=
  let s := trimSpaces string
  let i := s.data.length
  let spaceCount := s.data.foldl (fun acc c => if c == ' ' then acc + 1 else acc) 0
  let newLen := i + spaceCount * 2
  if newLen > MAX then
    "-1"
  else
    let resRev := s.data.foldl (fun acc c => if c == ' ' then '0' :: '2' :: '%' :: acc else c :: acc) []
    String.mk resRev.reverse

#guard replaceSpaces "My Name is Dawood" = "My%20Name%20is%20Dawood"
#guard replaceSpaces "I am a Programmer" = "I%20am%20a%20Programmer"
#guard replaceSpaces "I love Coding" = "I%20love%20Coding"
