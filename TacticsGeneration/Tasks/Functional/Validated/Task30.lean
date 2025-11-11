import Batteries
open Std

def checkEquality (s : String) : Bool :=
  s.data.headD ' ' == s.data.reverse.headD ' '

def countSubstringWithEqualEnds (s : String) : Nat :=
  let n := s.length
  let rec loop (i j result : Nat) : Nat :=
    if i < n then
      if j < n - i + 1 then
        let subStr := s.drop i |>.take j
        let newResult := if checkEquality subStr then result + 1 else result
        loop i (j + 1) newResult
      else
        loop (i + 1) 1 result
    else
        result
  loop 0 1 0

#guard countSubstringWithEqualEnds "abc" == 3
#guard countSubstringWithEqualEnds "abcda" == 6
#guard countSubstringWithEqualEnds "ab" == 2
