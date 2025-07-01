import Leancheck.Basic
import Leancheck.Arbitrary
import Std
open Std
---------------------------------------
def prop_addZeroNat (x : Nat) : Bool :=
  x + 0 == x
---------------------------------------
def prop_addZeroInt (x : Int) : Bool :=
  x + 0 == x
---------------------------------------
def prop_intIdempotentcy (x : Int) : Bool :=
  x * x == x
---------------------------------------
def prop_idempotentcy (x : Bool) : Bool :=
  and x x == x
---------------------------------------
def prop_float (x : Float) :=
  x - (1.0 / (2 ^ 64)) == x
---------------------------------------
def prop_listRevRev (x : List Int) :=
  List.reverse (List.reverse x) == x

def generate g :=
    let (len, g') := randNat g 0 2
    let rec loop (n : Nat) (acc : List Int) (g : StdGen) : List Int × StdGen :=
      match n with
      | 0 => (acc, g)
      | n + 1 =>
        let (x, g'') := Arbitrary.generate g
        loop n (x :: acc) g''
    loop len [] g'
---------------------------------------
def prop_arrayRevRev (x : Array Int) :=
  Array.reverse (Array.reverse x) == x
---------------------------------------


def main : IO Unit := do
  leanCheck prop_float (λ x => x > 0.01) (trials := 500)
  --leanCheck prop_listRevRev (trials := 3000)
  --leanCheck prop_arrayRevRev
  --leanCheck prop_listRevRev (some generate)
  --leanCheck prop_addZeroInt
  --leanCheck prop_intIdempotentcy

#eval main
