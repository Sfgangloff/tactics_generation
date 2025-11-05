import Batteries
open Std

def multipleSplit (text : String) : List String :=
  let delimiters : List Char := [';', ',', '*', '\n']
  let processChar (c : Char) (acc : List (List Char)) : List (List Char) :=
    if c ∈ delimiters then [] :: acc else
      match acc with
      | [] => [[c]]
      | h :: t => (c :: h) :: t
  text.toList.foldr processChar [[]] |>.reverse.map (fun chars => String.mk chars |>.trim)

#eval multipleSplit "Forces of the \ndarkness*are coming into the play." 
#eval multipleSplit "Mi Box runs on the \n Latest android*which has google assistance and chromecast." 
#eval multipleSplit "Certain services\nare subjected to change*over the seperate subscriptions."
