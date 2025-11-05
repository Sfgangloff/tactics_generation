import Batteries
open Std

def containsSubstr (text pat : String) : Bool := Id.run do
  let tlen := text.length
  let plen := pat.length
  if plen == 0 then
    return true
  if tlen < plen then
    return false
  for i in [0 : tlen - plen + 1] do
    let seg := (text.drop i).take plen
    if seg == pat then
      return true
  return false

def stringLiterals (patterns : List String) (text : String) : String := Id.run do
  for pattern in patterns do
    if containsSubstr text pattern then
      return "Matched!"
    else
      return "Not Matched!"
  
  return "Not Matched!"

#guard stringLiterals ["language"] "python language" = "Matched!"
#guard stringLiterals ["program"] "python language" = "Not Matched!"
#guard stringLiterals ["python"] "programming language" = "Not Matched!"
