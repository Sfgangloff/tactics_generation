import Batteries
open Std

def divisorsSum (n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => if n % (i + 1) == 0 then acc + (i + 1) else acc) 0

def amicableNumbersSum (limit : Nat) : Nat :=
  Id.run do
    let mut amicables := HashSet.empty
    for num in [2:limit + 1] do
      if !amicables.contains num then
        let sumFact := divisorsSum num
        let sumFact2 := divisorsSum sumFact
        if num == sumFact2 && num != sumFact then
          amicables := amicables.insert num
          amicables := amicables.insert sumFact
    return amicables.fold (fun acc x => acc + x) 0

#eval amicableNumbersSum 999 
#eval amicableNumbersSum 9999 
#eval amicableNumbersSum 99
