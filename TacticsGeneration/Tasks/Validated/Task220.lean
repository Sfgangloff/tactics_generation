import Batteries

open Std

def replaceMaxSpecialchar (text : String) (n : Nat) : String :=
  let (rev, _) := text.data.foldl
    (fun (s : List Char × Nat) ch =>
      let (acc, cnt) := s
      if cnt < n && (ch = ' ' || ch = ',' || ch = '.') then
        (':' :: acc, cnt + 1)
      else
        (ch :: acc, cnt)
    ) ([], 0)
  String.mk rev.reverse

#guard replaceMaxSpecialchar "Python language, Programming language." 2 = "Python:language: Programming language."
#guard replaceMaxSpecialchar "a b c,d e f" 3 = "a:b:c:d e f"
#guard replaceMaxSpecialchar "ram reshma,ram rahim" 1 = "ram:reshma,ram rahim"
