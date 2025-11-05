import Batteries

open Std

def diffs (xs : List Int) : List Int :=
  match xs with
  | [] => []
  | [_] => []
  | x :: y :: ys => (y - x) :: diffs (y :: ys)

def Seq_Linear (seq_nums : List Int) : String :=
  match diffs seq_nums with
  | [] => "Non Linear Sequence"
  | d :: ds => if ds.all (fun x => x == d) then "Linear Sequence" else "Non Linear Sequence"

#guard Seq_Linear [0,2,4,6,8,10] = "Linear Sequence"
#guard Seq_Linear [1,2,3] = "Linear Sequence"
#guard Seq_Linear [1,5,2] = "Non Linear Sequence"
