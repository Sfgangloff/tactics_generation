import Batteries

open Std

def replace (string : String) (char : String) : String :=
  let n := char.length
  if n == 0 then
    string
  else
    let rec go (s : String) (acc : String) (fuel : Nat) : String :=
      match fuel with
      | 0 => acc
      | Nat.succ fuel' =>
        if s.length == 0 then acc
        else
          if s.take n == char then
            let rec cnt (t : String) (k : Nat) (fuel2 : Nat) : (String × Nat) :=
              match fuel2 with
              | 0 => (t, k)
              | Nat.succ fuel2' =>
                if t.take n == char then
                  cnt (t.drop n) (k+1) fuel2'
                else
                  (t, k)
            let pr := cnt s 0 (s.length + 1)
            let rest := pr.fst
            go rest (acc ++ char) fuel'
          else
            go (s.drop 1) (acc ++ s.take 1) fuel'
    go string "" (string.length + 1)

#guard replace "peep" "e" == "pep"
#guard replace "Greek" "e" == "Grek"
#guard replace "Moon" "o" == "Mon"
