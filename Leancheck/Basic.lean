import Std

import Leancheck.Arbitrary
import Leancheck.Shrinking

open Std

structure TestOutput (α : Type) where
  runs   : Nat      := 0
  iter   : Nat      := 0
  ex     : Option α := none
  shrink : Option α := none
deriving Inhabited

-- TODO: Prove termination
/-
  Main method to check a property of a function
-/
set_option linter.unusedVariables false in 
partial def leanCheck {α: Type} [Arbitrary α] [ToString α] [Shrinking α]
  (prop : α → Bool)
  (cond : α → Bool := λ x => true)
  (generator : (Option (StdGen → α × StdGen)) := none)
  (trials : Nat := 100)
  (iteration : Nat := 0)
  (fails : Nat := 0) : TestOutput α := Id.run do 

  -- Check if done
  if iteration = trials then return { runs := trials, iter := iteration }

  -- Get generator and value
  let g := mkStdGen
  let gen := generator.getD Arbitrary.generate
  let (x,g') := gen g

  -- Check conditional
  if ¬ cond x then
    if fails <= 5 then
      leanCheck prop cond generator trials iteration (fails + 1)
    else
      leanCheck prop cond generator trials (iteration + 1) 0
  else
    -- Check property
    if ¬ prop x then
      let ex : TestOutput α := { runs := trials, iter := 0, ex := some x }

      if ¬ prop (Shrinking.shrink x) then
        return {ex with shrink := some (Shrinking.shrink x)}
      else
        return ex
    else 
      leanCheck prop cond generator trials (iteration + 1) 0

/-
  Parse TestOutput and print human-readable version
-/
def parseTestOutput (x : TestOutput α) [ToString α] : IO Unit :=
  match x with
  | { runs := _ , iter := _ , ex := none   , shrink := _ }      => IO.println s!"Success: {x.runs} tests passed"
  | { runs := _ , iter := _ , ex := some a , shrink := none }   => IO.println s!"Failure: Counterexample {a} found, not shrinkable"
  | { runs := _ , iter := _ , ex := some a , shrink := some b } => IO.println s!"Failure: Counterexample {a} found, shrinkable to {b}"
