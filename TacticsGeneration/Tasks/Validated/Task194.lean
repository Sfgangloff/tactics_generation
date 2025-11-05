import Batteries

open Std

def octal_To_Decimal (n : Nat) : Nat :=
  let rec go (temp base dec : Nat) : Nat :=
    if temp = 0 then dec
    else
      let last_digit := temp % 10
      let temp2 := temp / 10
      let dec2 := dec + last_digit * base
      let base2 := base * 8
      go temp2 base2 dec2
  go n 1 0

#guard octal_To_Decimal 25 = 21
#guard octal_To_Decimal 30 = 24
#guard octal_To_Decimal 40 = 32
