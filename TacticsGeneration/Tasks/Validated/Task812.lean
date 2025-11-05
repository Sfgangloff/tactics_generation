import Batteries

open Std

def road_rd (street : String) : String :=
  let n := street.length
  if street.drop (n - 4) == "Road" then
    street.take (n - 4) ++ "Rd."
  else
    street

#guard road_rd "ravipadu Road" == "ravipadu Rd."
#guard road_rd "palnadu Road" == "palnadu Rd."
#guard road_rd "eshwar enclave Road" == "eshwar enclave Rd."
