import Batteries
open Std

def multiplesOfNum (m n : Nat) : List Nat :=
  (List.range m).map (λ i => n * (i + 1))

#guard multiplesOfNum 4 3 == [3, 6, 9, 12]
#guard multiplesOfNum 2 5 == [5, 10]
#guard multiplesOfNum 9 2 == [2, 4, 6, 8, 10, 12, 14, 16, 18]
