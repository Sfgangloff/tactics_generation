import Batteries
open Std

def last (arr : List Int) (x : Int) (n : Nat) : Int :=
  let rec loop (low high res : Int) (fuel : Nat) : Int :=
    match fuel with
    | 0 => res
    | Nat.succ fuel' =>
      if low ≤ high then
        let mid : Int := (low + high) / 2
        let v : Int := arr.getD (Int.toNat mid) 0
        if v > x then
          loop low (mid - 1) res fuel'
        else if v < x then
          loop (mid + 1) high res fuel'
        else
          loop (mid + 1) high mid fuel'
      else
        res
  loop 0 (Int.ofNat n - 1) (-1) n

#guard last [1,2,3] 1 3 = 0
#guard last [1,1,1,2,3,4] 1 6 = 2
#guard last [2,3,2,3,6,8,9] 3 8 = 3
