import Batteries

open Std

def isUpperAscii (c : Char) : Bool := ('A' ≤ c) && (c ≤ 'Z')

def removeUppercase (str1 : String) : String :=
  let filtered := str1.data.filter (fun c => !(isUpperAscii c))
  String.mk filtered

#guard removeUppercase "cAstyoUrFavoRitETVshoWs" == "cstyoravoitshos"
#guard removeUppercase "wAtchTheinTernEtrAdIo" == "wtchheinerntrdo"
#guard removeUppercase "VoicESeaRchAndreComMendaTionS" == "oiceachndreomendaion"
