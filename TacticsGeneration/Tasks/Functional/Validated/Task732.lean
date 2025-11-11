import Batteries

open Std

def replace_specialchar (text : String) : String :=
  text.map (fun c => if c == ' ' || c == ',' || c == '.' then ':' else c)

#guard replace_specialchar "Python language, Programming language." == "Python:language::Programming:language:"
#guard replace_specialchar "a b c,d e f" == "a:b:c:d:e:f"
#guard replace_specialchar "ram reshma,ram rahim" == "ram:reshma:ram:rahim"
