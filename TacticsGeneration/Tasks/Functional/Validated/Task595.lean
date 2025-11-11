import Batteries

open Std

def mismatchCount (s1 s2 : String) : Nat :=
  let rec go (l1 l2 : List Char) (acc : Nat) :=
    match l1, l2 with
    | c1::t1, c2::t2 =>
        let acc' := if c1 == c2 then acc else acc + 1
        go t1 t2 acc'
    | _, _ => acc
  go s1.data s2.data 0

def min_Swaps (str1 str2 : String) : Sum Nat String :=
  let count := mismatchCount str1 str2
  if count % 2 == 0 then
    Sum.inl (count / 2)
  else
    Sum.inr "Not Possible"

#guard min_Swaps "1101" "1110" = Sum.inl 1
#guard min_Swaps "111" "000" = Sum.inr "Not Possible"
#guard min_Swaps "111" "110" = Sum.inr "Not Possible"
