import Batteries

open Std

def capitalizeWord (s : String) : String :=
  if s.length = 0 then ""
  else
    let first := s.take 1
    let rest := s.drop 1
    let firstUp := first.map (fun c => c.toUpper)
    let restLow := rest.map (fun c => c.toLower)
    firstUp ++ restLow

def snakeToCamel (word : String) : String :=
  let parts := word.splitOn "_"
  parts.foldl (fun acc x =>
    let cap := capitalizeWord x
    let piece := if cap == "" then "_" else cap
    acc ++ piece
  ) ""

#guard snakeToCamel "android_tv" == "AndroidTv"
#guard snakeToCamel "google_pixel" == "GooglePixel"
#guard snakeToCamel "apple_watch" == "AppleWatch"
