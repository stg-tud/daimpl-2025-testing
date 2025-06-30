import Std

import Leancheck.Arbitrary

open Std

/--
Checks a given property (`prop : Int → Bool`) by running it on 100 randomly generated `Int`s
in the interval `[0, 100]`.

Parameters:
- prop: Property to test
- cond Conditional for gnerated test cases
- generator: Generator to use
- trials: Amount of tests to run

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
def leanCheck {α: Type} [Arbitrary α] [ToString α]
  (prop : α → Bool)
  (cond : α → Bool := λ x : α => true)
  (generator : (Option (StdGen → α × StdGen)) := none)
  (trials : Nat := 100) : IO Unit := do

  let mut failed : Bool := false
  let mut g := mkStdGen
  let gen := generator.getD Arbitrary.generate

  for _ in [:trials] do
    let (x, g') := gen g
    g := g'
    if ¬ prop x then
      failed := true
      IO.println s!"Failed on {x}"
      return

  if ¬ failed then
    IO.println s!"Ok, passed {trials} tests."
