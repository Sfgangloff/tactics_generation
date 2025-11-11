import Batteries

open Std

def Array.modify2d {α : Type} (a : Array (Array α)) (y x : Nat) (f : α → α) :=
  a.modify y (fun row => row.modify x f)

def Array.set2d? {α : Type} (a : Array (Array α)) (y x : Nat) (value : α) :=
  a.modify2d y x (fun _ => value)

def Array.get2d {α : Type} (a : Array (Array α)) (y x : Nat) (fallback : α) :=
  (a.getD y #[]).getD x fallback

def maxSum (tri : List (List Nat)) (n : Nat) : Nat := Id.run do
  let mut t : Array (Array Nat) := tri.toArray.map (fun row => row.toArray)
  if n > 1 then
    let v00 := t.get2d 0 0 0
    let v11 := t.get2d 1 1 0
    t := t.set2d? 1 1 (v11 + v00)
    let v10 := t.get2d 1 0 0
    t := t.set2d? 1 0 (v10 + v00)
  for i in [2 : n] do
    let v_i0 := t.get2d i 0 0
    let v_im1_0 := t.get2d (i-1) 0 0
    t := t.set2d? i 0 (v_i0 + v_im1_0)
    let v_ii := t.get2d i i 0
    let v_im1_im1 := t.get2d (i-1) (i-1) 0
    t := t.set2d? i i (v_ii + v_im1_im1)
    for j in [1 : i] do
      let cur := t.get2d i j 0
      let a := cur + t.get2d (i-1) (j-1) 0
      let b := cur + t.get2d (i-1) j 0
      if a >= b then
        t := t.set2d? i j a
      else
        t := t.set2d? i j b
  let lastRow := t.getD (n-1) #[]
  let mut m : Nat := 0
  for x in lastRow do
    if x > m then m := x
  return m

#guard maxSum [[1], [2,1], [3,3,2]] 3 = 6
#guard maxSum [[1], [1, 2], [4, 1, 12]] 3 = 15
#guard maxSum [[2], [3,2], [13,23,12]] 3 = 28
