import Batteries

open Std

def min_Swaps (s1 s2 : String) : Int :=
  let rec loop (l1 l2 : List Char) (c0 c1 : Nat) : Nat × Nat :=
    match l1, l2 with
    | c :: t1, d :: t2 =>
      let c0' := if (c == '0' && d == '1') then c0 + 1 else c0
      let c1' := if (c == '1' && d == '0') then c1 + 1 else c1
      loop t1 t2 c0' c1'
    | _, _ => (c0, c1)
  let (c0, c1) := loop s1.data s2.data 0 0
  let result : Nat := c0 / 2 + c1 / 2
  if c0 % 2 == 0 && c1 % 2 == 0 then
    Int.ofNat result
  else if (c0 + c1) % 2 == 0 then
    Int.ofNat (result + 2)
  else
    (-1)

#guard min_Swaps "0011" "1111" = (1 : Int)
#guard min_Swaps "00011" "01001" = (2 : Int)
#guard min_Swaps "111" "111" = (0 : Int)
