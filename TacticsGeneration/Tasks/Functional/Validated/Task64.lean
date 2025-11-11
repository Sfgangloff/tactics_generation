import Batteries

open Std

def removeOne [BEq α] (xs : List α) (x : α) : List α :=
  match xs with
  | [] => []
  | y :: ys => if y == x then ys else y :: removeOne ys x

def findMinBySecond (xs : List (String × Nat)) : Option (String × Nat) :=
  match xs with
  | [] => none
  | x :: xt =>
    some <| xt.foldl (fun acc y => if y.snd ≤ acc.snd then y else acc) x

def selectionSortBySecond (xs : List (String × Nat)) : List (String × Nat) :=
  let n := xs.length
  let rec loop (ys : List (String × Nat)) (acc : List (String × Nat)) (fuel : Nat) : List (String × Nat) :=
    match fuel with
    | 0 => acc.reverse  
    | fuel' + 1 =>
      match ys with
      | [] => acc.reverse
      | _ =>
        match findMinBySecond ys with
        | none => acc.reverse
        | some m =>
          let ys' := removeOne ys m
          loop ys' (m :: acc) fuel'
  loop xs [] n

def subjectMarks (subjectmarks : List (String × Nat)) : List (String × Nat) :=
  selectionSortBySecond subjectmarks

#guard subjectMarks [("English", 88), ("Science", 90), ("Maths", 97), ("Social sciences", 82)] == [("Social sciences", 82), ("English", 88), ("Science", 90), ("Maths", 97)]
#guard subjectMarks [("Telugu",49),("Hindhi",54),("Social",33)] == [("Social",33),("Telugu",49),("Hindhi",54)]
#guard subjectMarks [("Physics",96),("Chemistry",97),("Biology",45)] == [("Biology",45),("Physics",96),("Chemistry",97)]
