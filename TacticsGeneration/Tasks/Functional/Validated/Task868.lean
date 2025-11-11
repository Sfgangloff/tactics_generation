import Batteries

open Std

def length_Of_Last_Word (a : String) : Nat :=
  let parts := a.splitOn " "
  let rec go (l : List String) (lastLen : Nat) : Nat :=
    match l with
    | [] => lastLen
    | s :: t =>
      let lastLen' := if s == "" then lastLen else s.length
      go t lastLen'
  go parts 0

#guard length_Of_Last_Word "python language" = 8
#guard length_Of_Last_Word "PHP" = 3
#guard length_Of_Last_Word "" = 0
