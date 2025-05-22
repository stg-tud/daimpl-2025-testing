import Leancheck.Basic
import Leancheck.Arbitrary
import Std
open Std

def prop_addZeroNat (x : Nat) : Bool :=
  x + 0 == x

def prop_addZeroInt (x : Int) : Bool :=
  x + 0 == x

def prop_idempotentcy (x : Bool) : Bool :=
  and x x == x

def prop_listRevRev (x : List Int) :=
  List.reverse (List.reverse x) == x

def main : IO Unit :=
  leanCheck prop_idempotentcy
