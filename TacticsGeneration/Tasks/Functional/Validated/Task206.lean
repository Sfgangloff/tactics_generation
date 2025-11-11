import Batteries

open Std

def concatenateElements (test_tup : List String) : List String :=
  (List.zip test_tup (test_tup.drop 1)).map (fun p => p.fst ++ p.snd)

#guard concatenateElements ["DSP ", "IS ", "BEST ", "FOR ", "ALL ", "UTS"] = ["DSP IS ", "IS BEST ", "BEST FOR ", "FOR ALL ", "ALL UTS"]
#guard concatenateElements ["RES ", "IS ", "BEST ", "FOR ", "ALL ", "QESR"] = ["RES IS ", "IS BEST ", "BEST FOR ", "FOR ALL ", "ALL QESR"]
#guard concatenateElements ["MSAM", "IS ", "BEST ", "FOR ", "ALL ", "SKD"] = ["MSAMIS ", "IS BEST ", "BEST FOR ", "FOR ALL ", "ALL SKD"]
