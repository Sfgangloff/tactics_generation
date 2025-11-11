import Batteries

open Std

def Array.modify3d {α : Type} (a : Array (Array (Array α))) (i j k : Nat) (f : α → α) :=
  a.modify i (fun row2 => row2.modify j (fun row1 => row1.modify k f))

def Array.set3d? {α : Type} (a : Array (Array (Array α))) (i j k : Nat) (value : α) :=
  a.modify3d i j k (fun _ => value)

def Array.get3d {α : Type} (a : Array (Array (Array α))) (i j k : Nat) (fallback : α) :=
  ((a.getD i #[]).getD j #[]).getD k fallback

def lcsOfThree (X Y Z : String) (m n o : Nat) : Nat := Id.run do
  
  let Xa := X.data.toArray
  let Ya := Y.data.toArray
  let Za := Z.data.toArray
  let mut L : Array (Array (Array Nat)) :=
    Array.replicate (m+1) (Array.replicate (n+1) (Array.replicate (o+1) 0))
  for i in [0 : m+1] do
    for j in [0 : n+1] do
      for k in [0 : o+1] do
        if i == 0 || j == 0 || k == 0 then
          L := L.set3d? i j k 0
        else if Xa[i-1]! == Ya[j-1]! && Xa[i-1]! == Za[k-1]! then
          let v := L.get3d (i-1) (j-1) (k-1) 0 + 1
          L := L.set3d? i j k v
        else
          let a := L.get3d (i-1) j k 0
          let b := L.get3d i (j-1) k 0
          let c := L.get3d i j (k-1) 0
          L := L.set3d? i j k (Nat.max (Nat.max a b) c)
  return L.get3d m n o 0

#guard lcsOfThree "AGGT12" "12TXAYB" "12XBA" 6 7 5 = 2
#guard lcsOfThree "Reels" "Reelsfor" "ReelsforReels" 5 8 13 = 5
#guard lcsOfThree "abcd1e2" "bc12ea" "bd1ea" 7 6 5 = 3
