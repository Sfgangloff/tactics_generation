import Batteries

open Std

def min_Swaps (str1 str2 : String) : Sum Nat String :=
  
  let l1 := str1.data
  let l2 := str2.data
  let count := (List.zip l1 l2).foldl (init := 0) (fun acc p =>
    match p with
    | (a, b) => if a == b then acc else acc + 1)
  if count % 2 == 0 then
    Sum.inl (count / 2)
  else
    Sum.inr "Not Possible"

#guard min_Swaps "1101" "1110" == Sum.inl 1
#guard min_Swaps "1111" "0100" == Sum.inr "Not Possible"
#guard min_Swaps "1110000" "0001101" == Sum.inl 3
