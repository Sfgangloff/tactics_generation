import Batteries

open Std

def remove_duplic_list (l : List String) : List String :=
  let rec go (l acc : List String) : List String :=
    match l with
    | [] => acc.reverse
    | x :: xs =>
      if acc.contains x then
        go xs acc
      else
        go xs (x :: acc)
  go l []

#guard remove_duplic_list ["Python", "Exercises", "Practice", "Solution", "Exercises"]
  == ["Python", "Exercises", "Practice", "Solution"]
#guard remove_duplic_list ["Python", "Exercises", "Practice", "Solution", "Exercises", "Java"]
  == ["Python", "Exercises", "Practice", "Solution", "Java"]
#guard remove_duplic_list ["Python", "Exercises", "Practice", "Solution", "Exercises", "C++", "C", "C++"]
  == ["Python", "Exercises", "Practice", "Solution", "C++", "C"]
