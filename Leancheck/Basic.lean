import Std

import Leancheck.Arbitrary
import Leancheck.Shrinking

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
partial def leanCheckCore {α: Type} [Arbitrary α] [ToString α] [Shrinking α]
  (prop : α → Bool)
  (cond : α → Bool := λ _ => true)
  (generatorFunc : StdGen → α × StdGen)
  (g : StdGen)
  (trials : Nat := 100)
  (iteration : Nat := 0)
  (fails : Nat := 0) : TestOutput α := Id.run do

  -- Check if done
  if iteration = trials then return { trial := trials, iter := iteration }

  -- Get generator and value
  let (x, g') := generatorFunc g

  -- Check conditional
  if ¬ cond x then
    if fails = 5 then
      return { trial := trials, iter := iteration, timeout := true}
    else
      leanCheckCore prop cond generatorFunc g' (trials + 1) iteration (fails + 1)
  else
    -- Check property
    if ¬ prop x then
      let ex : TestOutput α := { trial := trials, ex := some x }

      if ¬ prop (Shrinking.shrink x) then
        return {ex with shrink := some (Shrinking.shrink x)}
      else
        return ex
    else
      leanCheckCore prop cond generatorFunc g' trials (iteration + 1)

/-
  Parse TestOutput and print human-readable version
-/
def parseTestOutput (name : String) (x : TestOutput α) [ToString α] : IO Unit :=
  match x with
  | { trial := _ , iter := _ , ex := _      , shrink := _ , timeout := true } => IO.println s!"Failure \"{name}\": Tests have timed out. {x.iter}/{x.trial} have been tested"
  | { trial := _ , iter := _ , ex := none   , shrink := _ , timeout := false}      => IO.println s!"Success \"{name}\": {x.iter}/{x.trial} passed"
  | { trial := _ , iter := _ , ex := some a , shrink := none  , timeout := false}   => IO.println s!"Failure \"{name}\": Counterexample {a} found, not shrinkable"
  | { trial := _ , iter := _ , ex := some a , shrink := some b  , timeout := false} => IO.println s!"Failure \"{name}\": Counterexample {a} found, shrinkable to {b}"

def leanCheck {α: Type} [Arbitrary α] [ToString α] [Shrinking α]
  (name : String)
  (prop : α → Bool)
  (cond : α → Bool := λ _ => true)
  (generator : (Option (StdGen → α × StdGen)) := none)
  (trials : Nat := 100) : IO Unit := do

  let g := mkStdGen
  let gen := generator.getD Arbitrary.generate

  parseTestOutput name $ leanCheckCore prop cond gen g trials (iteration := 0) (fails := 0)
