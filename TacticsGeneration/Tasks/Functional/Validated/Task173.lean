import Batteries

open Std

def remove_splchar (text : String) : String :=
  text.foldl (init := "") (fun acc c => if Char.isAlphanum c then acc.push c else acc)

#guard remove_splchar "python  @#&^%$*program123" == "pythonprogram123"
#guard remove_splchar "python %^$@!^&*()  programming24%$^^()    language" == "pythonprogramming24language"
#guard remove_splchar "python   ^%&^()(+_)(_^&67)                  program" == "python67program"
