import Batteries

open Std

partial def permuteString (s : String) : List String :=
  if s.length == 0 then [""]
  else
    let prev := permuteString (s.drop 1)
    let c := s.take 1
    prev.foldl (fun acc p =>
      (List.range s.length).foldl (fun acc2 j =>
        let newStr := p.take j ++ c ++ p.drop j
        if acc2.any (fun x => x == newStr) then acc2 else acc2 ++ [newStr]
      ) acc
    ) []

#guard permuteString "ab" == ["ab", "ba"]
#guard permuteString "abc" == ["abc", "bac", "bca", "acb", "cab", "cba"]
#guard permuteString "abcd" == ["abcd", "bacd", "bcad", "bcda", "acbd", "cabd", "cbad", "cbda", "acdb", "cadb", "cdab", "cdba", "abdc", "badc", "bdac", "bdca", "adbc", "dabc", "dbac", "dbca", "adcb", "dacb", "dcab", "dcba"]
