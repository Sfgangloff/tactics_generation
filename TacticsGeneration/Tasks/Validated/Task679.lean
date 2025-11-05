import Batteries
open Std

private def getAt? {α : Type u} (xs : List α) (i : Nat) : Option α :=
  match xs, i with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs', Nat.succ j => getAt? xs' j

def accessKey (ditionary : List (String × Nat)) (key : Nat) : String :=
  match getAt? ditionary key with
  | some (s, _) => s
  | none => ""

#guard accessKey [("physics",80),("math",90),("chemistry",86)] 0 = "physics"
#guard accessKey [("python",10),("java",20),("C++",30)] 2 = "C++"
#guard accessKey [("program",15),("computer",45)] 1 = "computer"
