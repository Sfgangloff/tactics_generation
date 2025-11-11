import Batteries

open Std

def listCmpNatList (a b : List Nat) : Ordering :=
  match a, b with
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | x::xs, y::ys =>
    if x < y then .lt
    else if x > y then .gt
    else listCmpNatList xs ys

def maxLength (list1 : List (List Nat)) : Nat × List Nat := Id.run do
  match list1 with
  | [] => return (0, [])
  | first :: rest =>
    let mut maxLen := first.length
    let mut maxList := first
    for xs in rest do
      if xs.length > maxLen then
        maxLen := xs.length
      match listCmpNatList xs maxList with
      | .gt => maxList := xs
      | _ => ()
    return (maxLen, maxList)

#guard maxLength [[0], [1, 3], [5, 7], [9, 11], [13, 15, 17]] = (3, [13, 15, 17])
#guard maxLength [[1], [5, 7], [10, 12, 14, 15]] = (4, [10, 12, 14, 15])
#guard maxLength [[5], [15, 20, 25]] = (3, [15, 20, 25])
