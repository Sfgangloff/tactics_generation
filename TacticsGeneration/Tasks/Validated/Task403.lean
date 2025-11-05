import Batteries

open Std

def lastOfList (l : List String) (d : String) : String :=
  match l with
  | [] => d
  | [x] => x
  | _::xs => lastOfList xs d

def allLowerAlpha (s : String) : Bool :=
  s.data.all (fun c =>
    let n := c.toNat
    Nat.ble 97 n && Nat.ble n 122
  )

def hasSpace (s : String) : Bool :=
  s.data.any (fun c => c == ' ')

def isValidURL (s : String) : Bool :=
  let hasHttp := s.startsWith "http://"
  let hasHttps := s.startsWith "https://"
  if !hasHttp && !hasHttps then
    false
  else
    let rest :=
      if hasHttp then s.drop ("http://".length) else s.drop ("https://".length)
    if hasSpace rest then
      false
    else
      let rest' := if rest.startsWith "www." then rest.drop ("www.".length) else rest
      let host := (rest'.splitOn "/").headD rest'
      let parts := host.splitOn "."
      if Nat.blt parts.length 2 then false else
        let tld := lastOfList parts ""
        let tldLen := tld.length
        if (Nat.blt tldLen 2) || (Nat.blt 6 tldLen) then false else
          allLowerAlpha tld

#guard isValidURL "https://www.google.com" == true
#guard isValidURL "https:/www.gmail.com" == false
#guard isValidURL "https:// www.redit.com" == false
