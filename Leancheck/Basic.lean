import Std

import Leancheck.Arbitrary
import Leancheck.ManualShrinking

open Std

structure TestOutput (α : Type) where
  trial   : Nat      := 0
  iter    : Nat      := 0
  ex      : Option α := none
  shrink  : Option α := none
  timeout : Bool     := false
deriving Inhabited

/--
  Main method to check a property of a function
-/
def leanCheckCore {α : Type} [Arbitrary α] [ToString α] [ManualShrinking α]
  (prop : α → Bool)
  (map : α → α := id)
  (generatorFunc : StdGen → α × StdGen)
  (shrinkingFunc : α → (prop : α → Bool) → (map : α → α) → Option α)
  (g0 : StdGen)
  (trials : Nat) : TestOutput α :=

  let rec loop : Nat → StdGen → TestOutput α
    -- Check if done
    | 0, _ =>
      { trial := trials, iter := trials }
    | (n+1), g =>
      -- Get generator and value
      let (x, g') := generatorFunc g
      let y := map x
      -- Check property
      if ¬ prop y then
        let iteration := trials - (n+1)
        let shrinked := shrinkingFunc x prop map
        { trial := trials, iter := iteration, ex := some y, shrink := shrinked }
      else
        loop n g'
  loop trials g0

/--
  Parse TestOutput and print human-readable version
-/
def parseTestOutput {α : Type} (name : String) (x : TestOutput α) [ToString α] : IO Unit :=
  match x with
  | { trial := _ , iter := _ , ex := _      , shrink := _      , timeout := true } => IO.println s!"Failure \"{name}\": Tests have timed out. {x.iter}/{x.trial} have been tested"
  | { trial := _ , iter := _ , ex := none   , shrink := _      , timeout := false} => IO.println s!"Success \"{name}\": {x.iter}/{x.trial} passed"
  | { trial := _ , iter := _ , ex := some a , shrink := none   , timeout := false} => IO.println s!"Failure \"{name}\": Counterexample {a} found, not shrinkable"
  | { trial := _ , iter := _ , ex := some a , shrink := some b , timeout := false} => IO.println s!"Failure \"{name}\": Counterexample {a} found, shrinkable to {b}"

/-
  Evaluate test output
-/
def evalTestOutput {α : Type} (c : TestOutput α) : Bool :=
  match c with
  | { trial := _ , iter := _ , ex := _      , shrink := _       , timeout := true } => false
  | { trial := _ , iter := _ , ex := none   , shrink := _       , timeout := false} => true
  | { trial := _ , iter := _ , ex := some _ , shrink := none    , timeout := false} => false
  | { trial := _ , iter := _ , ex := some _ , shrink := some _  , timeout := false} => false


/-
  Evaluate a singular
-/
def leanCheck {α : Type} [Arbitrary α] [ToString α] [ManualShrinking α]
  (name : String)
  (prop : α → Bool)
  (map : α → α := id)
  (generator : (Option (StdGen → α × StdGen)) := none)
  (shrinker : (Option (α → (prop : α → Bool) → (map : α → α) → Option α)) := none)
  (trials : Nat := 100)
  (seed : Nat := 0) : IO Unit := do

  let g := mkStdGen seed
  let generatorFunc := generator.getD Arbitrary.generate
  let shrinkingFunc := shrinker.getD ManualShrinking.shrink

  parseTestOutput name $ leanCheckCore prop map generatorFunc shrinkingFunc g trials

def postulate {α: Type} [Arbitrary α] [ToString α] [ManualShrinking α]
  (prop : α → Bool)
  (map : α → α := id)
  (generator : (Option (StdGen → α × StdGen)) := none)
  (shrinker : (Option (α → (prop : α → Bool) → (map : α → α) → Option α)) := none)
  (trials : Nat := 100)
  (seed : Nat := 0) : Prop := 

  let g := mkStdGen seed
  let generatorFunc := generator.getD Arbitrary.generate
  let shrinkingFunc := shrinker.getD ManualShrinking.shrink

  evalTestOutput $ leanCheckCore prop map generatorFunc shrinkingFunc g trials
