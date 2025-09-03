import Std

import Leancheck.Arbitrary
import Leancheck.ManualShrinking

open Std

structure TestOutput (α : Type) where
  trial    : Nat      := 0
  iter    : Nat      := 0
  ex      : Option α := none
  shrink  : Option α := none
  timeout : Bool     := false
deriving Inhabited

-- TODO: Prove termination
/-
  Main method to check a property of a function
-/
partial def leanCheckCore {α: Type} [Arbitrary α] [ToString α] [ManualShrinking α]
  (prop : α → Bool)
  (map : α → α := id)
  (generatorFunc : StdGen → α × StdGen)
  (shrinkingFunc : α → (prop : α → Bool) → (map : α → α) → α)
  (g : StdGen)
  (trials : Nat := 100)
  (iteration : Nat := 0) : TestOutput α := Id.run do

  -- Check if done
  if iteration = trials then return { trial := trials, iter := iteration }

  -- Get generator and value
  let (x, g') := generatorFunc g
  let y := map x

  -- Check property
    if ¬ prop y then
      let ex : TestOutput α := { trial := trials, ex := some y }

      if ¬ prop (shrinkingFunc x prop map) then
        return {ex with shrink := some (shrinkingFunc x prop map)}
      else
        return ex
    else
      leanCheckCore prop map generatorFunc shrinkingFunc g' trials (iteration + 1)

/-
  Parse TestOutput and print human-readable version
-/
def parseTestOutput{α: Type} (x : TestOutput α) [ToString α] : IO Unit :=
  match x with
  | { trial := _ , iter := _ , ex := _      , shrink := _ , timeout := true } => IO.println s!"Failure: Tests have timed out. {x.iter}/{x.trial} have been tested"
  | { trial := _ , iter := _ , ex := none   , shrink := _ , timeout := false}      => IO.println s!"Success: {x.iter}/{x.trial} passed"
  | { trial := _ , iter := _ , ex := some a , shrink := none  , timeout := false}   => IO.println s!"Failure: Counterexample {a} found, not shrinkable"
  | { trial := _ , iter := _ , ex := some a , shrink := some b  , timeout := false} => IO.println s!"Failure: Counterexample {a} found, shrinkable to {b}"

def leanCheck {α: Type} [Arbitrary α] [ToString α] [ManualShrinking α]
  (prop : α → Bool)
  (map : α → α := id)
  (generator : (Option (StdGen → α × StdGen)) := none)
  (shrinker : (Option (α → (prop : α → Bool) → (map : α → α) → α)) := none)
  (trials : Nat := 100) : IO Unit := do

  let g := mkStdGen
  let generatorFunc := generator.getD Arbitrary.generate
  let shrinkingFunc := shrinker.getD ManualShrinking.shrink

  parseTestOutput $ leanCheckCore prop map generatorFunc shrinkingFunc g trials (iteration := 0)
