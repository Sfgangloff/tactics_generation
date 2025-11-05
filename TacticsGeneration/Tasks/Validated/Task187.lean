import Batteries

open Std

partial def longestCommonSubsequence (X Y : String) (m n : Nat) : Nat :=
  if m == 0 || n == 0 then 0
  else
    let xLast := (X.take m).drop (m - 1)
    let yLast := (Y.take n).drop (n - 1)
    if xLast == yLast then
      1 + longestCommonSubsequence X Y (m - 1) (n - 1)
    else
      let a := longestCommonSubsequence X Y m (n - 1)
      let b := longestCommonSubsequence X Y (m - 1) n
      if a >= b then a else b

#guard longestCommonSubsequence "AGGTAB" "GXTXAYB" 6 7 = 4
#guard longestCommonSubsequence "ABCDGH" "AEDFHR" 6 6 = 3
#guard longestCommonSubsequence "AXYT" "AYZX" 4 4 = 2
