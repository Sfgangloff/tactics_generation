import Batteries

open Std

def extractNthElement (list1 : List (String × Nat × Nat)) (n : Nat) : List (Sum String Nat) :=
  match n with
  | 0 => list1.map (fun x => Sum.inl x.fst)
  | 1 => list1.map (fun x => Sum.inr x.snd.fst)
  | 2 => list1.map (fun x => Sum.inr x.snd.snd)
  | _ => []

#guard extractNthElement [("Greyson Fulton", (98, 99)), ("Brady Kent", (97, 96)), ("Wyatt Knott", (91, 94)), ("Beau Turnbull", (94, 98))] 0
  == [Sum.inl "Greyson Fulton", Sum.inl "Brady Kent", Sum.inl "Wyatt Knott", Sum.inl "Beau Turnbull"]

#guard extractNthElement [("Greyson Fulton", (98, 99)), ("Brady Kent", (97, 96)), ("Wyatt Knott", (91, 94)), ("Beau Turnbull", (94, 98))] 2
  == [Sum.inr 99, Sum.inr 96, Sum.inr 94, Sum.inr 98]

#guard extractNthElement [("Greyson Fulton", (98, 99)), ("Brady Kent", (97, 96)), ("Wyatt Knott", (91, 94)), ("Beau Turnbull", (94, 98))] 1
  == [Sum.inr 98, Sum.inr 97, Sum.inr 91, Sum.inr 94]
