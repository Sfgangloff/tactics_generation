import Batteries

open Std

def findDemlo (s : String) : String := Id.run do
  let l := s.length
  let mut res := ""
  for i in [1 : l+1] do
    res := res ++ toString i
  let mut i := l - 1
  while i > 0 do
    res := res ++ toString i
    i := i - 1
  return res

#guard findDemlo "111111" = "12345654321"
#guard findDemlo "1111" = "1234321"
#guard findDemlo "13333122222" = "123456789101110987654321"
