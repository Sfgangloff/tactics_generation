import Batteries

open Std

def re_arrange_array (arr : List Int) (n : Nat) : List Int := Id.run do
  
  let mut a := arr.toArray
  let mut j : Nat := 0
  for i in [: n] do
    let xi := a[i]!
    if xi < 0 then
      let temp := xi
      let yj := a[j]!
      a := a.set! i yj
      a := a.set! j temp
      j := j + 1
  return a.toList

#guard re_arrange_array [-1, 2, -3, 4, 5, 6, -7, 8, 9] 9 == [-1, -3, -7, 4, 5, 6, 2, 8, 9]
#guard re_arrange_array [12, -14, -26, 13, 15] 5 == [-14, -26, 12, 13, 15]
#guard re_arrange_array [10, 24, 36, -42, -39, -78, 85] 7 == [-42, -39, -78, 10, 24, 36, 85]
