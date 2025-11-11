import Batteries
open Std

private def updateCount (c : Char) (counts : List (Char × Nat)) : (List (Char × Nat) × Nat) :=
  let rec upd (l : List (Char × Nat)) : (List (Char × Nat) × Nat) :=
    match l with
    | [] => ([(c, 1)], 1)
    | (d, n) :: rs =>
      if d = c then
        ((d, n + 1) :: rs, n + 1)
      else
        let (rs', cnt) := upd rs
        ((d, n) :: rs', cnt)
  upd counts

def maxChar (str1 : String) : Char := Id.run do
  
  let mut counts : List (Char × Nat) := []
  let mut best : Char := ' '
  let mut bestCount : Nat := 0
  for c in str1.data do
    let (counts', cnt) := updateCount c counts
    counts := counts'
    if cnt > bestCount then
      best := c
      bestCount := cnt
  return best

#guard maxChar "hello world" == 'l'
#guard maxChar "hello " == 'l'
#guard maxChar "python pr" == 'p'
