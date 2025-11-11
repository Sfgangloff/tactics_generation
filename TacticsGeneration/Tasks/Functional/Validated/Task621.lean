import Batteries

open Std

private def parseNatDigits (s : String) : Option Nat :=
  if s.length == 0 then none else
  let rec loop (cs : List Char) (acc : Nat) : Option Nat :=
    match cs with
    | [] => some acc
    | c :: cs' =>
      if '0' ≤ c && c ≤ '9' then
        let digit := c.toNat - '0'.toNat
        loop cs' (acc * 10 + digit)
      else
        none
  loop s.data 0

def increment_numerics (test_list : List String) (K : Nat) : List String :=
  test_list.map (fun ele =>
    match parseNatDigits ele with
    | some n => toString (n + K)
    | none => ele)

#guard increment_numerics ["MSM", "234", "is", "98", "123", "best", "4"] 6 == ["MSM", "240", "is", "104", "129", "best", "10"]
#guard increment_numerics ["Dart", "356", "is", "88", "169", "Super", "6"] 12 == ["Dart", "368", "is", "100", "181", "Super", "18"]
#guard increment_numerics ["Flutter", "451", "is", "44", "96", "Magnificent", "12"] 33 == ["Flutter", "484", "is", "77", "129", "Magnificent", "45"]
