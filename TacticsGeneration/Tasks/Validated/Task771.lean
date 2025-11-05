import Batteries

open Std

def checkExpression (exp : String) : Bool := Id.run do
  let chars := exp.data
  let n := chars.length
  if (n &&& 1) == 1 then
    return false
  let mut stack : List Char := []
  for ch in chars do
    if ch == '(' || ch == '{' || ch == '[' then
      stack := ch :: stack
    if ch == ')' || ch == '}' || ch == ']' then
      if stack.isEmpty then
        return false
      let top := stack.head!
      stack := stack.tail!
      if (top == '(' && ch != ')') || (top == '{' && ch != '}' || (top == '[' && ch != ']')) then
        return false
  return stack.isEmpty

#guard checkExpression "{()}[{}]" == true
#guard checkExpression "{()}[{]" == false
#guard checkExpression "{()}[{}][]({})" == true
