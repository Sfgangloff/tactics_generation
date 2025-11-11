import Batteries

open Std

def removeWhitespaces (text1 : String) : String :=
  String.mk (text1.toList.filter (fun c => !c.isWhitespace))

#guard removeWhitespaces " Google    Flutter " == "GoogleFlutter"
#guard removeWhitespaces " Google    Dart " == "GoogleDart"
#guard removeWhitespaces " iOS    Swift " == "iOSSwift"
