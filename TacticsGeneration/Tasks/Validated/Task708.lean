import Batteries

open Std

def Convert (string : String) : List String :=
  string.splitOn " "

#guard Convert "python program" == ["python", "program"]
#guard Convert "Data Analysis" == ["Data", "Analysis"]
#guard Convert "Hadoop Training" == ["Hadoop", "Training"]
