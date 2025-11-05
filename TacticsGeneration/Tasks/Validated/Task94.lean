import Batteries
open Std

def indexMinimum (testList : List (String × Nat)) : String :=
  match testList.foldl (fun acc x => if x.snd < acc.snd then x else acc) ("", Nat.succ $ testList.foldl (fun acc x => max acc x.snd) 0) with
  | (res, _) => res

#guard indexMinimum [("Rash", 143), ("Manjeet", 200), ("Varsha", 100)] == "Varsha"
#guard indexMinimum [("Yash", 185), ("Dawood", 125), ("Sanya", 175)] == "Dawood"
#guard indexMinimum [("Sai", 345), ("Salman", 145), ("Ayesha", 96)] == "Ayesha"
