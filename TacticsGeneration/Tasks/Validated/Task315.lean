import Batteries

open Std

def find_Max_Len_Even (s : String) : String := Id.run do
  let tokens := s.splitOn " "
  let mut maxlen := 0
  let mut best : String := ""
  let mut found := false
  for w in tokens do
    let l := w.length
    if l % 2 == 0 then
      if maxlen < l then
        maxlen := l
        best := w
        found := true
  if found then
    return best
  else
    return "-1"

#guard find_Max_Len_Even "python language" == "language"
#guard find_Max_Len_Even "maximum even length" == "length"
#guard find_Max_Len_Even "eve" == "-1"
