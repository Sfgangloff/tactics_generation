import Batteries

open Std

def isAsciiAlnum (c : Char) : Bool :=
  let n := c.toNat
  (n >= '0'.toNat && n <= '9'.toNat) ||
  (n >= 'A'.toNat && n <= 'Z'.toNat) ||
  (n >= 'a'.toNat && n <= 'z'.toNat)

def removeChar (S : String) : String :=
  String.mk (S.data.filter isAsciiAlnum)

#guard removeChar "123abcjw:, .@! eiw" == "123abcjweiw"
#guard removeChar "Hello1234:, ! Howare33u" == "Hello1234Howare33u"
#guard removeChar "Cool543Triks@:, Make@987Trips" == "Cool543TriksMake987Trips"
