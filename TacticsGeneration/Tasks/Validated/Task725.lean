import Batteries

open Std

structure QuotState where
  inQuote : Bool
  buf : List Char
  resRev : List String
  deriving Inhabited

def extract_quotation (text1 : String) : List String :=
  let step (st : QuotState) (c : Char) : QuotState :=
    if st.inQuote then
      if c = '"' then
        { inQuote := false
        , buf := []
        , resRev := (String.mk st.buf.reverse) :: st.resRev }
      else
        { st with buf := c :: st.buf }
    else
      if c = '"' then
        { inQuote := true, buf := [], resRev := st.resRev }
      else
        st
  let s := text1.data.foldl step {inQuote := false, buf := [], resRev := []}
  s.resRev.reverse

#guard extract_quotation "Cortex \"A53\" Based \"multi\" tasking \"Processor\"" == ["A53", "multi", "Processor"]
#guard extract_quotation "Cast your \"favorite\" entertainment \"apps\"" == ["favorite", "apps"]
#guard extract_quotation "Watch content \"4k Ultra HD\" resolution with \"HDR 10\" Support" == ["4k Ultra HD", "HDR 10"]
