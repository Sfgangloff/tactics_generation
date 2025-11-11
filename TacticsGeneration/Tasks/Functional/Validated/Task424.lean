import Batteries

open Std

def extractRear (testTuple : List String) : List String :=
  testTuple.map (fun s => (s.drop (s.length - 1)).take 1)

#guard extractRear ["Mers", "for", "Vers"] == ["s", "r", "s"]
#guard extractRear ["Avenge", "for", "People"] == ["e", "r", "e"]
#guard extractRear ["Gotta", "get", "go"] == ["a", "t", "o"]
