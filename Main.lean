import Leancheck.Basic
open Leancheck

def prop_addZero (x : Int) : Bool :=
  x + 0 == x

def prop_div (x : Int) : Option Bool :=
  if x ≠ 0 then some (x / x == 1) else none

def main : IO Unit :=
  --leanCheck prop_addZero
  leanCheckOptional prop_div
