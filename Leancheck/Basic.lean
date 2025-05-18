import Std

open Std

/--
Generates a random `Int` in the interval `[lo, hi]` using the given `StdGen`.

Returns a pair `(x, g')` where:
- `x` is the random integer in the desired range
- `g'` is the updated random generator
-/
def randIntInRange (g : StdGen) (lo hi : Int) : Int × StdGen :=
  let (n, g') := randNat g (lo.toNat) (hi.toNat)
  (Int.ofNat n, g')

/--
Generates a list of length `len` of random `Int`s in the interval `[lo, hi]`.

Returns a pair `(xs, g')` where:
- `xs` is the list of random integers
- `g'` is the updated random generator after generating all elements
-/
def randIntList (g : StdGen) (len : Nat) (lo hi : Int) : List Int × StdGen :=
  match len with
  | 0 => ([], g)
  | n + 1 =>
    let (x, g1) := randIntInRange g lo hi
    let (xs, g2) := randIntList g1 n lo hi
    (x :: xs, g2)

/--
Generates a list of length `len` of random `Int`s in the interval `[lo, hi]`.

Returns a pair `(xs, g')` where:
- `xs` is the list of random integers
- `g'` is the updated random generator after generating all elements
-/
def randIntListIteratively (g : StdGen) (len : Nat) (lo hi : Int) : List Int × StdGen := Id.run do
  let mut g := g
  let mut lst := []
  for _ in [0:len] do
    let (x, g') := randIntInRange g lo hi
    lst := x :: lst -- append element to beginning bc of performance
    g := g'
  (lst, g)

/--
Checks a given property (`prop : Int → Bool`) by running it on 100 randomly generated `Int`s
in the interval `[0, 100]`.

Prints:
- A failure message for each failing input
- A success message if all tests pass

Usage:
```lean
def prop_addZero (x : Int) : Bool :=
  x + 0 == x

def main : IO Unit :=
  leanCheck prop_addZero
```
-/
def leanCheck (prop : Int → Bool) : IO Unit := do
  let mut failed : Bool := false
  let g := mkStdGen
  let (lst, _) := randIntListIteratively g 100 0 100
  for x in lst do
    if ¬ prop x then
      failed := true
      IO.println s!"Failed on {x}"

  if ¬ failed then
    IO.println "Ok, passed 100 tests."
