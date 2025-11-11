import Batteries

open Std

def averageOdd (n : Nat) : Sum String Nat :=
  if n % 2 == 0 then
    .inl "Invalid Input"
  else
    let rec accumOdd : Nat -> Nat × Nat
      | 0 => (0, 0)
      | 1 => (1, 1)
      | Nat.succ (Nat.succ k) =>
        let (sm, cnt) := accumOdd k
        (sm + (k + 2), cnt + 1)
    let (sm, cnt) := accumOdd n
    .inr (sm / cnt)

#guard averageOdd 9 = .inr 5
#guard averageOdd 5 = .inr 3
#guard averageOdd 11 = .inr 6
