import Batteries
open Std

def uniqueSublists {α} [BEq α] [Hashable α] (list1 : List (List α)) : Std.HashMap (List α) Nat := Id.run do
  
  let mut result : Std.HashMap (List α) (List Nat) := {}
  for l in list1 do
    let key := l
    let existing :=
      let rec loop (xs : List ((List α) × (List Nat))) : List Nat :=
        match xs with
        | [] => []
        | (k', v) :: t =>
          if k' == key then v else loop t
      loop result.toList
    result := result.insert key (existing ++ [1])
  
  let mut result2 : Std.HashMap (List α) Nat := {}
  for (k, v) in result.toList do
    let s := v.foldl (fun acc x => acc + x) 0
    result2 := result2.insert k s
  return result2

def getOrDefault {κ υ} [BEq κ] [Hashable κ] (m : Std.HashMap κ υ) (k : κ) (d : υ) : υ :=
  let rec loop (xs : List (κ × υ)) : υ :=
    match xs with
    | [] => d
    | (k', v) :: t => if k == k' then v else loop t
  loop m.toList

#guard (let r := uniqueSublists [[1, 3], [5, 7], [1, 3], [13, 15, 17], [5, 7], [9, 11]];
  getOrDefault r [1, 3] 0 = 2 ∧
  getOrDefault r [5, 7] 0 = 2 ∧
  getOrDefault r [13, 15, 17] 0 = 1 ∧
  getOrDefault r [9, 11] 0 = 1 ∧
  r.size = 4)

#guard (let r := uniqueSublists [["green", "orange"], ["black"], ["green", "orange"], ["white"]];
  getOrDefault r ["green", "orange"] 0 = 2 ∧
  getOrDefault r ["black"] 0 = 1 ∧
  getOrDefault r ["white"] 0 = 1 ∧
  r.size = 3)

#guard (let r := uniqueSublists [[10, 20, 30, 40], [60, 70, 50, 50], [90, 100, 200]];
  getOrDefault r [10, 20, 30, 40] 0 = 1 ∧
  getOrDefault r [60, 70, 50, 50] 0 = 1 ∧
  getOrDefault r [90, 100, 200] 0 = 1 ∧
  r.size = 3)
