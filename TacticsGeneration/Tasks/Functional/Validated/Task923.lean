import Batteries

open Std

partial def superSeq (X Y : String) (m n : Nat) : Nat :=
  if m = 0 then n
  else if n = 0 then m
  else
    let xm1 := (X.drop (m - 1)).take 1
    let yn1 := (Y.drop (n - 1)).take 1
    if xm1 = yn1 then
      1 + superSeq X Y (m - 1) (n - 1)
    else
      1 + min (superSeq X Y (m - 1) n) (superSeq X Y m (n - 1))

#guard superSeq "AGGTAB" "GXTXAYB" 6 7 = 9
#guard superSeq "feek" "eke" 4 3 = 5
#guard superSeq "PARRT" "RTA" 5 3 = 6
