import Batteries

open Std

def joinWith (sep : String) (xs : List String) : String :=
  match xs with
  | [] => ""
  | x :: xs' => xs'.foldl (fun acc s => acc ++ sep ++ s) x

def tupleString (l : List Nat) : String :=
  "(" ++ joinWith ", " (l.map toString) ++ ")"

def updateCounts (acc : List (List Nat × Nat)) (k : List Nat) : List (List Nat × Nat) :=
  let (found, rev) :=
    acc.foldl
      (fun (p : Bool × List (List Nat × Nat)) (e : List Nat × Nat) =>
        let found := p.1
        let rev := p.2
        let k' := e.1
        let n  := e.2
        if !found && k' == k then
          (true, (k', n+1) :: rev)
        else
          (found, e :: rev)
      )
      (false, [])
  let acc' := rev.reverse
  if found then acc' else acc' ++ [(k, 1)]

def assignFreq (testList : List (List Nat)) : String :=
  let counts := testList.foldl updateCounts []
  let itemsStrs := counts.map (fun (k, n) => tupleString (k ++ [n]))
  "[" ++ joinWith ", " itemsStrs ++ "]"

#guard assignFreq [[6, 5, 8], [2, 7], [6, 5, 8], [6, 5, 8], [9], [2, 7]] = "[(6, 5, 8, 3), (2, 7, 2), (9, 1)]"
#guard assignFreq [[4, 2, 4], [7, 1], [4, 8], [4, 2, 4], [9, 2], [7, 1]] = "[(4, 2, 4, 2), (7, 1, 2), (4, 8, 1), (9, 2, 1)]"
#guard assignFreq [[11, 13, 10], [17, 21], [4, 2, 3], [17, 21], [9, 2], [4, 2, 3]] = "[(11, 13, 10, 1), (17, 21, 2), (4, 2, 3, 2), (9, 2, 1)]"
