import Batteries

open Std

def removeLowercase (str1 : String) : String :=
  let remove_lower := fun (text : String) =>
    let filtered := text.data.filter (fun c =>
      let n := c.toNat
      not (n >= 'a'.toNat && n <= 'z'.toNat))
    String.mk filtered
  let result := remove_lower str1
  result

#guard removeLowercase "KDeoALOklOOHserfLoAJSIskdsf" = "KDALOOOHLAJSI"
#guard removeLowercase "ProducTnamEstreAmIngMediAplAYer" = "PTEAIMAAY"
#guard removeLowercase "maNufacTuredbYSheZenTechNolOGIes" = "NTYSZTNOGI"
