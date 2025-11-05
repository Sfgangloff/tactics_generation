import Batteries
open Std

def wordTitle (w : String) : String :=
  if w.length = 0 then ""
  else
    let first := w.take 1
    let rest := w.drop 1
    first.toUpper ++ rest.toLower

def capitalizeFirstLastLetters (str1 : String) : String := Id.run do
  let words0 := str1.splitOn " "
  let words := words0.filter (fun w => w != "")
  let titleWords := words.map wordTitle
  let mut result := ""
  for word in titleWords do
    let len := word.length
    if len = 0 then
      result := result ++ " "
    else
      result := result ++ (word.take (len - 1)) ++ ((word.drop (len - 1)).toUpper) ++ " "
  if result.length = 0 then
    return ""
  else
    return result.take (result.length - 1)

#guard capitalizeFirstLastLetters "python" == "PythoN"
#guard capitalizeFirstLastLetters "bigdata" == "BigdatA"
#guard capitalizeFirstLastLetters "Hadoop" == "HadooP"
