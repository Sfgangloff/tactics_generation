import Batteries
open Std

def removeFirst [BEq α] (y : α) (xs : List α) : List α :=
  let rec loop (ys : List α) (removed : Bool) : List α :=
    match ys with
    | [] => []
    | x :: xt =>
      if !removed && x == y then
        xt
      else
        x :: loop xt removed
  loop xs false

def listMinChar (xs : List Char) (init : Char) : Char :=
  xs.foldl (fun m x => if x < m then x else m) init

def selectionSortChar (xs : List Char) : List Char :=
  let rec sel (fuel : Nat) (ys acc : List Char) : List Char :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      match ys with
      | [] => acc
      | _ =>
        let m := listMinChar ys (ys.headD '0')
        let ys' := removeFirst m ys
        sel fuel' ys' (acc ++ [m])
  sel xs.length xs []

def rearrangeBigger (n : Nat) : Option Nat := Id.run do
  let s := toString n
  let mut arr := s.data.toArray
  let len := arr.size
  if len < 2 then
    return none
  let mut found := false
  let mut pivot := 0
  let mut i := len - 2
  while true do
    if arr[i]! < arr[i+1]! then
      found := true
      pivot := i
      break
    if i == 0 then
      break
    i := i - 1
  if !found then
    return none
  let zList := (arr.extract pivot len).toList
  let z0 := zList.headD '0'
  let candidates := zList.filter (fun x => x > z0)
  if candidates.isEmpty then
    return none
  let y := listMinChar candidates (candidates.headD z0)
  let zRemoved := removeFirst y zList
  let zSorted := selectionSortChar zRemoved
  let prefixList := (arr.extract 0 pivot).toList
  let newList : List Char := prefixList ++ (y :: zSorted)
  let newStr := String.mk newList
  match String.toNat? newStr with
  | some k => return some k
  | none => return none

#guard rearrangeBigger 12 == some 21
#guard rearrangeBigger 10 == none
#guard rearrangeBigger 102 == some 120
