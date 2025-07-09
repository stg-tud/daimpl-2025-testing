import Std

import Leancheck.Arbitrary
import Leancheck.Shrinking

open Std

-- TODO: Update description
/--
Checks a given property (`prop : Int → Bool`) by running it on 100 randomly generated `Int`s
in the interval `[0, 100]`.

Parameters:
- prop: Property to test
- cond: Property for generated test cases
- generator: Generator to use
- trials: Amount of tests to run

Prints:
- A failure message for each failing input
- A message for test cases failing the conditional
- A success message if all tests pass and info about the conditional

Usage:
```lean
def prop_addZero (x : Int) : Bool :=
  x + 0 == x

def main : IO Unit :=
  leanCheck prop_addZero
```
-/
def leanCheck {α: Type} [Arbitrary α] [ToString α] [Shrinking α]
  (prop : α → Bool)
  (cond : α → Bool := λ x => true)
  (generator : (Option (StdGen → α × StdGen)) := none)
  (trials : Nat := 100) : IO Unit := do

  let mut failed : Bool := false
  let mut g := mkStdGen
  let gen := generator.getD Arbitrary.generate

  -- TODO Write the logic more functional
  let mut timeout := 0

  for _ in [:trials] do
    let mut fail : Nat := 0
    let mut (x, g') := gen g
    g := g'

    while ¬ cond x do 
      (x,g') := gen g
      g := g'
      fail := fail + 1
      IO.println s!"Filter {x}"

      if fail = 5 then
        fail := 0
        timeout := timeout + 1
        break 

    if ¬ prop x then
      failed := true
      let xShrinked := Shrinking.shrink x
      IO.println s!"Failed on {x} shrinked to {xShrinked}"
      return


  if ¬ failed then
    IO.println s!"Ok, passed {trials - timeout} tests. {timeout} tests have timed out"
