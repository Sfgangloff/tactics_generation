import Batteries
open Std

def removeOcc (s : String) (ch : Char) : String := Id.run do
  let mut str := s
  for i in [0 : str.length] do
    if str.data[i]? == some ch then
      str := (str.take i) ++ (str.drop (i + 1))
      break
  for i in (List.range str.length).reverse do
    if str.data[i]? == some ch then
      str := (str.take i) ++ (str.drop (i + 1))
      break
  return str

#guard removeOcc "hello" 'l' == "heo"
#guard removeOcc "abcda" 'a' == "bcd"
#guard removeOcc "PHP" 'P' == "H"
#guard removeOcc "hellolloll" 'l' == "helollol"
#guard removeOcc "" 'l' == ""
