import Batteries

open Std

private def format0 (template : String) (arg : String) : String :=
  match template.splitOn "{0}" with
  | [] => ""
  | p :: ps => ps.foldl (fun acc s => acc ++ arg ++ s) p

def add_string {α} [ToString α] (list : List α) (string : String) : List String :=
  list.map (fun i => format0 string (toString i))

#guard add_string [1,2,3,4] "temp{0}" == ["temp1", "temp2", "temp3", "temp4"]
#guard add_string ["a","b","c","d"] "python{0}" == ["pythona", "pythonb", "pythonc", "pythond"]
#guard add_string [5,6,7,8] "string{0}" == ["string5", "string6", "string7", "string8"]
