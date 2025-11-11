import Batteries
open Std

def snakeToCamel (word : String) : String :=
  word.splitOn "_" |>.map String.capitalize |>.foldl (· ++ ·) ""

#guard snakeToCamel "python_program" == "PythonProgram"
#guard snakeToCamel "python_language" == "PythonLanguage"
#guard snakeToCamel "programming_language" == "ProgrammingLanguage"
