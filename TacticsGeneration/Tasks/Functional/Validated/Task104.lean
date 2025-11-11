import Batteries

open Std

def insertBy (cmp : α → α → Bool) (x : α) (xs : List α) : List α :=
  match xs with
  | [] => [x]
  | y :: ys => if cmp x y then x :: y :: ys else y :: insertBy cmp x ys

def isort (cmp : α → α → Bool) (xs : List α) : List α :=
  List.foldr (insertBy cmp) [] xs

def sortSublists (inputList : List (List String)) : List (List String) :=
  inputList.map (isort (fun x y => x.front < y.front))

#eval sortSublists [["green", "orange"], ["black", "white"], ["white", "black", "orange"]] == [["green", "orange"], ["black", "white"], ["black", "orange", "white"]]
#eval sortSublists [[" red ","green" ],["blue "," black"],[" orange","brown"]] == [[" red ", "green"], [" black", "blue "], [" orange", "brown"]]
#eval sortSublists [["zilver","gold"], ["magnesium","aluminium"], ["steel", "bronze"]] == [["gold", "zilver"],["aluminium", "magnesium"], ["bronze", "steel"]]
