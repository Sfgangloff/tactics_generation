import Batteries

open Std

def make_flip (ch : String) : String :=
  if ch == "0" then "1" else "0"

def get_flip_with_starting_charcter (str : String) (expected : String) : Nat := Id.run do
  let n := str.length
  let mut flip_count := 0
  let mut exp := expected
  for i in [: n] do
    let ch := (str.drop i).take 1
    if ch != exp then
      flip_count := flip_count + 1
    exp := make_flip exp
  return flip_count

def min_flip_to_make_string_alternate (str : String) : Nat :=
  min (get_flip_with_starting_charcter str "0") (get_flip_with_starting_charcter str "1")

#guard min_flip_to_make_string_alternate "0001010111" == 2
#guard min_flip_to_make_string_alternate "001" == 1
#guard min_flip_to_make_string_alternate "010111011" == 2
