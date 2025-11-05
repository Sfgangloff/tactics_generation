import Batteries

open Std

def repeatAppend (acc s : String) (k : Nat) : String :=
  match k with
  | 0 => acc
  | Nat.succ k' => repeatAppend (acc ++ s) s k'

def int_to_roman (num : Nat) : String := Id.run do
  let val : Array Nat := #[1000, 900, 500, 400, 100, 90, 50, 40, 10, 9, 5, 4, 1]
  let syb : Array String := #["M", "CM", "D", "CD", "C", "XC", "L", "XL", "X", "IX", "V", "IV", "I"]
  let mut roman_num := ""
  let mut n := num
  for i in [: val.size] do
    let v := val[i]!
    let s := syb[i]!
    let q := n / v
    if q > 0 then
      roman_num := repeatAppend roman_num s q
      n := n % v
  return roman_num

#guard int_to_roman 1 = "I"
#guard int_to_roman 50 = "L"
#guard int_to_roman 4 = "IV"
