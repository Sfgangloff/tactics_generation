import Batteries
open Std

def containsBEq [BEq α] : List α → α → Bool
  | [], _ => false
  | y :: ys, x => if y == x then true else containsBEq ys x

def dedupPreserve [BEq β] (xs : List β) : List β :=
  let rec loop (seen : List β) (accRev : List β) (ys : List β) : List β :=
    match ys with
    | [] => accRev.reverse
    | y :: ys' =>
      if containsBEq seen y then
        loop seen accRev ys'
      else
        loop (y :: seen) (y :: accRev) ys'
  loop [] [] xs

def sortOnOccurence [BEq α] [BEq β]
  (lst : List (α × β)) : List (α × List β × Nat) :=
  let acc : List (α × List β) :=
    lst.foldl
      (init := ([] : List (α × List β)))
      (fun acc pr =>
        let i := pr.fst
        let j := pr.snd
        let rec go (xs : List (α × List β)) (preRev : List (α × List β)) : List (α × List β) :=
          match xs with
          | [] => preRev.reverse ++ [(i, [j])]
          | (k, vs) :: tl =>
            if k == i then
              preRev.reverse ++ ((k, vs ++ [j]) :: tl)
            else
              go tl ((k, vs) :: preRev)
        go acc [])
  acc.map (fun (i, js) =>
    let uniq := dedupPreserve js
    (i, uniq, js.length))

#guard sortOnOccurence [(1, "Jake"), (2, "Bob"), (1, "Cara")] = [(1, ["Jake", "Cara"], 2), (2, ["Bob"], 1)]
#guard sortOnOccurence [("b", "ball"), ("a", "arm"), ("b", "b"), ("a", "ant")] = [("b", ["ball", "b"], 2), ("a", ["arm", "ant"], 2)]
#guard sortOnOccurence [(2, "Mark"), (3, "Maze"), (2, "Sara")] = [(2, ["Mark", "Sara"], 2), (3, ["Maze"], 1)]
