/-
  This is a file containing some basic tests with the library
  Either execute `lake test` for a comprehensive view or look into the source file
-/

import Leancheck
import Std

open Std

-- Define properties or custom generators
def prop_addZeroNat (x : Nat) : Bool :=
  x + 0 == x

def prop_addZeroInt (x : Int) : Bool :=
  x + 0 == x + 1

def prop_intIdempotentcy (x : Int) : Bool :=
  x * x == x

def prop_idempotentcy (x : Bool) : Bool :=
  and x x == x

def prop_float (x : Float) :=
  x - (1.0 / (2 ^ 64)) == x

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

def prop_arrayRevRev (x : Array Int) :=
  Array.reverse (Array.reverse x) == x

def prop_revConcat (x: List Int × List Int) :=
  let (x1, x2) := x
  List.reverse (x1 ++ x2) == List.reverse x1 ++ List.reverse x2

def main := do
  leanCheck (λ x => x + 1 = x + 1)
  leanCheck (λ x => x + 1 = x + 1)
  leanCheck (λ x => x + 1 = x + 0)
  leanCheck prop_float (λ x => x > 20) (trials := 500)
  leanCheck prop_listRevRev
  leanCheck prop_revConcat
  leanCheck prop_arrayRevRev
  leanCheck prop_listRevRev (generator := some generate)
  leanCheck prop_addZeroInt
  leanCheck prop_intIdempotentcy

#eval main
