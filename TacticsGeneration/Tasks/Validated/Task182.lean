import Batteries

open Std

def lettersFrom (start : Char) (len : Nat) : List Char :=
  (List.range len).map (fun i => Char.ofNat (start.toNat + i))

def charSetFrom (start : Char) (len : Nat) : HashSet Char :=
  HashSet.ofList (lettersFrom start len)

def uppercaseSet : HashSet Char := charSetFrom 'A' 26
def lowercaseSet : HashSet Char := charSetFrom 'a' 26
def digitSet     : HashSet Char := charSetFrom '0' 10
def specialSet   : HashSet Char := HashSet.ofList [',', ' ', '.', '!', '?']

def charToString (c : Char) : String := String.mk [c]

def find_character (s : String) : (List String × List String × List String × List String) := Id.run do
  let mut ups : List String := []
  let mut lows : List String := []
  let mut nums : List String := []
  let mut specs : List String := []
  for c in s.data do
    if c ∈ uppercaseSet then
      ups := (charToString c) :: ups
    else if c ∈ lowercaseSet then
      lows := (charToString c) :: lows
    else if c ∈ digitSet then
      nums := (charToString c) :: nums
    else if c ∈ specialSet then
      specs := (charToString c) :: specs
    else
      pure ()
  return (ups.reverse, lows.reverse, nums.reverse, specs.reverse)

#guard find_character "ThisIsGeeksforGeeks" == (["T", "I", "G", "G"], ["h", "i", "s", "s", "e", "e", "k", "s", "f", "o", "r", "e", "e", "k", "s"], [], [])
#guard find_character "Hithere2" == (["H"], ["i", "t", "h", "e", "r", "e"], ["2"], [])
#guard find_character "HeyFolks32" == (["H", "F"], ["e", "y", "o", "l", "k", "s"], ["3", "2"], [])
