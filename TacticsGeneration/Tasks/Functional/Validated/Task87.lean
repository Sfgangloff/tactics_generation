import Batteries
open Std

def mergeDictionariesThree (dict1 dict2 dict3 : HashMap String String) : HashMap String String := Id.run do
  let mut m : HashMap String String := {}

  for (k, v) in dict3.toList do
    m := m.insert k v
  for (k, v) in dict2.toList do
    m := m.insert k v
  for (k, v) in dict1.toList do
    m := m.insert k v
  return m

def lookupInList {α β} [BEq α] (k : α) (l : List (α × β)) : Option β :=
  let rec go (l : List (α × β)) : Option β :=
    match l with
    | [] => none
    | (k2, v2) :: t => if k2 == k then some v2 else go t
  go l

def mapsEqual {α β} [BEq α] [Hashable α] [BEq β]
  (m1 : HashMap α β) (m2 : HashMap α β) : Bool := Id.run do
  if m1.size != m2.size then
    return false
  let l2 := m2.toList
  for (k, v) in m1.toList do
    match lookupInList k l2 with
    | some v2 => if v2 == v then pure () else return false
    | none => return false
  return true

def d1 : HashMap String String := HashMap.ofList [("R","Red"), ("B","Black"), ("P","Pink")]
def d2 : HashMap String String := HashMap.ofList [("G","Green"), ("W","White")]
def d3 : HashMap String String := HashMap.ofList [("O","Orange"), ("W","White"), ("B","Black")]
def expected1 : HashMap String String := HashMap.ofList [("B","Black"), ("R","Red"), ("P","Pink"), ("G","Green"), ("W","White"), ("O","Orange")]
#guard mapsEqual (mergeDictionariesThree d1 d2 d3) expected1

def d1b : HashMap String String := HashMap.ofList [("R","Red"), ("B","Black"), ("P","Pink")]
def d2b : HashMap String String := HashMap.ofList [("G","Green"), ("W","White")]
def d3b : HashMap String String := HashMap.ofList [("L","lavender"), ("B","Blue")]
def expected2 : HashMap String String := HashMap.ofList [("W","White"), ("P","Pink"), ("B","Black"), ("R","Red"), ("G","Green"), ("L","lavender")]
#guard mapsEqual (mergeDictionariesThree d1b d2b d3b) expected2

def d1c : HashMap String String := HashMap.ofList [("R","Red"), ("B","Black"), ("P","Pink")]
def d2c : HashMap String String := HashMap.ofList [("L","lavender"), ("B","Blue")]
def d3c : HashMap String String := HashMap.ofList [("G","Green"), ("W","White")]
def expected3 : HashMap String String := HashMap.ofList [("B","Black"), ("P","Pink"), ("R","Red"), ("G","Green"), ("L","lavender"), ("W","White")]
#guard mapsEqual (mergeDictionariesThree d1c d2c d3c) expected3
