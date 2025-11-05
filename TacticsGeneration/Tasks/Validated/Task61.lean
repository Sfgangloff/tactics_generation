import Batteries
open Std

def charDigit (s : String) : Nat :=
  if s == "0" then 0 else
  if s == "1" then 1 else
  if s == "2" then 2 else
  if s == "3" then 3 else
  if s == "4" then 4 else
  if s == "5" then 5 else
  if s == "6" then 6 else
  if s == "7" then 7 else
  if s == "8" then 8 else
  if s == "9" then 9 else 0

def countSubstrings (s : String) (n : Nat) : Nat := Id.run do
  let mut cnt : Nat := 0
  let mut sm : Int := 0
  let mut mp : Std.HashMap Int Nat := {}
  mp := mp.insert 0 1
  let mut ts := s
  for i in [: n] do
    let d := charDigit (ts.take 1)
    sm := sm + Int.ofNat d
    let diff : Int := sm - Int.ofNat (i + 1)
    let prev :=
      mp.fold (init := 0) (fun acc k v => if k == diff then v else acc)
    cnt := cnt + prev
    mp := mp.insert diff (prev + 1)
    ts := ts.drop 1
  return cnt

#guard countSubstrings "112112" 6 = 6
#guard countSubstrings "111" 3 = 6
#guard countSubstrings "1101112" 7 = 12
