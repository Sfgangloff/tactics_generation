import Batteries
open Std

def countChar (s : String) (x : Char) : Nat :=
  let n := 10
  let totalInS := s.data.foldl (fun acc c => if c == x then acc + 1 else acc) 0
  let len := s.length
  let repetitions := n / len
  let base := totalInS * repetitions
  let l := n % len
  let pref := s.take l
  let extra := pref.data.foldl (fun acc c => if c == x then acc + 1 else acc) 0
  base + extra

#guard countChar "abcac" 'a' == 4
#guard countChar "abca" 'c' == 2
#guard countChar "aba" 'a' == 7
