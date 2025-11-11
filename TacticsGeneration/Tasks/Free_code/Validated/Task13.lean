import Batteries
open Std

/-!
  Auto-generated from task 13.
  Module: Task13
-/

structure WordStat where
  word : String
  count : Nat
  first : Nat
  deriving BEq

/-- Count the most common words and return the top 4 as (word, count).
    Ties are broken by the earliest first occurrence in the input list. -/
def countCommon (words : List String) : List (String × Nat) :=
  -- Update an association list map with (word → (count, firstIndex))
  let rec upd (m : List (String × (Nat × Nat))) (w : String) (i : Nat) : List (String × (Nat × Nat)) :=
    match m with
    | [] => [(w, (1, i))]
    | (k, (c, f)) :: t =>
      if k == w then
        (k, (c + 1, f)) :: t
      else
        (k, (c, f)) :: upd t w i
  -- Build association list with counts and first indices
  let rec build (ws : List String) (i : Nat) (m : List (String × (Nat × Nat))) : List (String × (Nat × Nat)) :=
    match ws with
    | [] => m
    | w :: ws' =>
      let m' := upd m w i
      build ws' (i + 1) m'
  let assoc := build words 0 []
  -- Convert to stats
  let stats : List WordStat :=
    assoc.map (fun p =>
      let w := p.fst
      let cf := p.snd
      { word := w, count := cf.fst, first := cf.snd }
    )
  -- Better comparator (higher count, then smaller first index)
  let better (a b : WordStat) : Bool :=
    a.count > b.count || (a.count == b.count && a.first < b.first)
  -- Pick top k elements using the comparator
  let rec pickTop (ss : List WordStat) (k : Nat) : List (String × Nat) :=
    match k with
    | 0 => []
    | Nat.succ k' =>
      match ss with
      | [] => []
      | h :: t =>
        let best := List.foldl (fun b a => if better a b then a else b) h t
        let remaining := ss.filter (fun s => !(s.word == best.word))
        (best.word, best.count) :: pickTop remaining k'
  pickTop stats 4


-- Tests
#guard countCommon ["red","green","black","pink","black","white","black","eyes","white","black","orange","pink","pink","red","red","white","orange","white","black","pink","green","green","pink","green","pink","white","orange","orange","red"]
  == [("pink", 6), ("black", 5), ("white", 5), ("red", 4)]

#guard countCommon ["one", "two", "three", "four", "five", "one", "two", "one", "three", "one"]
  == [("one", 4), ("two", 2), ("three", 2), ("four", 1)]

#guard countCommon ["Facebook", "Apple", "Amazon", "Netflix", "Google", "Apple", "Netflix", "Amazon"]
  == [("Apple", 2), ("Amazon", 2), ("Netflix", 2), ("Facebook", 1)]