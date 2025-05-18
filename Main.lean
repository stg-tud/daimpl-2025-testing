import Leancheck.Basic

def prop_addZero (x : Int) : Bool :=
  x + 0 == x

def main : IO Unit :=
  leanCheck prop_addZero
