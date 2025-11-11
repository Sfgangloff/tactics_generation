import Batteries
open Std

def oddEquivalent (s : String) (n : Nat) : Nat :=
  let count := s.data.take n |>.filter (· == '1') |>.length
  count

#guard oddEquivalent "011001" 6 == 3
#guard oddEquivalent "11011" 5 == 4
#guard oddEquivalent "1010" 4 == 2
