import Batteries

open Std

def fillSpaces (text : String) : String :=
  String.mk <|
    text.data.map (fun c => if c == ' ' || c == ',' || c == '.' then ':' else c)

#guard fillSpaces "Boult Curve Wireless Neckband" == "Boult:Curve:Wireless:Neckband"
#guard fillSpaces "Stereo Sound Sweatproof" == "Stereo:Sound:Sweatproof"
#guard fillSpaces "Probass Curve Audio" == "Probass:Curve:Audio"
