import Batteries
open Std

private def insertBy (cmp : (String × Nat) → (String × Nat) → Bool) :
    (String × Nat) → List (String × Nat) → List (String × Nat)
  | a, [] => [a]
  | a, b :: bs => if cmp a b then a :: b :: bs else b :: insertBy cmp a bs

private def sortBy (cmp : (String × Nat) → (String × Nat) → Bool) :
    List (String × Nat) → List (String × Nat)
  | [] => []
  | b :: bs => insertBy cmp b (sortBy cmp bs)

def sortCounter (dict1 : List (String × Nat)) : List (String × Nat) :=
  sortBy (fun a b => decide (a.snd > b.snd)) dict1

#guard sortCounter [("Math",81), ("Physics",83), ("Chemistry",87)] == [("Chemistry", 87), ("Physics", 83), ("Math", 81)]
#guard sortCounter [("Math",400), ("Physics",300), ("Chemistry",250)] == [("Math", 400), ("Physics", 300), ("Chemistry", 250)]
#guard sortCounter [("Math",900), ("Physics",1000), ("Chemistry",1250)] == [("Chemistry", 1250), ("Physics", 1000), ("Math", 900)]
