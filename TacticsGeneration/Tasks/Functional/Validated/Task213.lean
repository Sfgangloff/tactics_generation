import Batteries

open Std

def concatenateStrings (testTup1 : List String) (testTup2 : List String) : List String :=
  List.zipWith (fun a b => a ++ b) testTup1 testTup2

#guard concatenateStrings ["Manjeet", "Nikhil", "Akshat"] [" Singh", " Meherwal", " Garg"] == ["Manjeet Singh", "Nikhil Meherwal", "Akshat Garg"]
#guard concatenateStrings ["Shaik", "Ayesha", "Sanya"] [" Dawood", " Begum", " Singh"] == ["Shaik Dawood", "Ayesha Begum", "Sanya Singh"]
#guard concatenateStrings ["Harpreet", "Priyanka", "Muskan"] ["Kour", " Agarwal", "Sethi"] == ["HarpreetKour", "Priyanka Agarwal", "MuskanSethi"]
