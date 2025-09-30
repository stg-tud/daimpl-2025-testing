# leancheck

`leancheck` is a property-based testing library akin to QuickCheck for Haskell. It includes test execution, generators and shrinking specification.

## Conceptual framework

Standard testing as done in most applications, specifically unit testing, specifies test cases (function inputs) and expected output per test case. This is carries some serious design problems:

- Test cases may be forgotten, like special edge cases with nullable types

- Enumeration of test cases is tedious for complex data structures

- Expected output does not imply expected behaviour

Property-based testing (PBT) solves those issues by relegating input specification to generators, i.e., automating which inputs are used for testing. Expected output is generalised by properties, describing program behaviour by boolean statements. If a property is violated, the generated input is a so called counterexample, with which debugging happens.

The paragraph above describes the essential components of PBT. In addition, many libraries implement a feature called Shrinking. By their random nature, counterexamples may be very big, like huge integers. The feature, in short, algorithmically reduces counterexamples into the smallest possible counterexample, making debugging significantly easier. There exist many approaches towards this with many up- and downsides regarding algorithmic complexity at runtime, implementation and memory concerns. We will discuss our approach on shrinking in the next section.

## Implementation 

The base of the library is in `basic.lean` where the core function of leancheck `leanCheckCore` and its wrapper fuction `leanCheck` are located. The wrapper function takes at minimum a name and a property to check. If the type α is a basic type, it may be inferred. If not, then more specification is necessary. This includes a random generator and a shrinker for elements of your type. Additionally you can provide the following arguments:

- `map : α → α := id`: A mapping function. This is useful if you want to only test numbers that fulfill specific conditions, e.g. you can pass `(fun x => x * 2)` when you want your property only to be checked with even numbers. Other test libraries call this "Conditional"

- `trials : Nat := 100`: Controls how many random inputs the checker will try for a property at most. Default is set to 100.

- `(seed : Nat := 0)`: The seed you want to use for the random generator.

- Properties, Generators and Shrinkers may be defined as necessary, the library itself implements basic types, arrays, lists and pairs

As mentioned before you do not have to provide a generator and shrinker for basic types like Bool, Nat, Int, List, Array and Pair, as the generators and shrinkers for these types are already implemented in the library and are automatically found by Lean's instance search.
But of course you still can provide your own generator and shrinker for basic types; see the following generator and test call below:
```haskell
-- Custom generator
def generate g :=
    let (len, g') := randNat g 0 2
    let rec loop (n : Nat) (acc : List Int) (g : StdGen) : List Int × StdGen :=
      match n with
      | 0 => (acc, g)
      | n + 1 =>
        let (x, g'') := Arbitrary.generate g
        loop n (x :: acc) g''
    loop len [] g'
    
leanCheck "Other generator" prop_listRevRev (generator := some generate)    
```

If you want to use leanCheck on a custom type the approach on passing a generator and a shrinker is a bit different, but we will talk about this in the Usage section.

Now let us take a look at the flow of leanCheck and how exactly the generators and shrinkers work together.
In `leanCheckCore`, each iteration draws a fresh sample `x : α` from the generator, applies the map to obtain `y`, and checks `prop y`. If `prop y` fails, the loop stops early and calls the provided shrinker with the original `x` (plus `prop` and `map`) to search for a smaller failing case. You may wonder why the shrinker does not take the mapped value directly and instead takes the original value and the mapping function. This is due to a fundamental issue in shrinking, which is how to choose the next smaller value. At first, this may seem trivial, but this is only the case for values that do not have to satisfy specific conditions. For example, if we only want to test even values, the shrinker somehow needs this information so that it doesn't accidentally shrink to an odd value. One approach would be to check on every shrinking step whether a shrunken value satisfies the condition, and if not, to discard it.  However, this would be inefficient, as we would have to discard, on average, every second number. This is why we decided to take a different approach, shrinking the unmapped values first and then mapping and testing whether the mapped value still fails the property. The only drawback is that this approach depends on the mapping function being monotonic, so that `x′ <= x ⇒ map(x′) <= map(x)`.

## Adding leancheck to your project

Add the following lines to your `lakefile.toml`:

```toml
testDriver = "Tests"

[[require]]
name = "leancheck"
git = "https://github.com/stg-tud/daimpl-2025-testing.git"

[[lean_exe]]
name = "Tests"
globs = ["Tests.+"]
```

Execute `lake update` and your ready to go. `./Leancheck/examples` contains a example config for starting out.

## Usage

The entire test tooling depends on function `leancheck`. At minimum, a name and a property have to be provided. Optionally, you can provide the arguments decribed in the section "Implementation". Support for custom types, i.e., generator, mapping function and shrinker, must be implemented separately, also stated in the sections prior.

For basic types you can just define a property, which is function that takes an argument of type α and returns a Bool (`prop : α → Bool`), and then pass it to the leanCheck function.

If you want to use leanCheck for custom types you also have to define a generator and a shrinker. But you cannot just pass them as an argument to the leanCheck function. Instead you have define a typeclass instance of `Arbitrary` and `ManualShrinking` so that Lean can synthesize `[Arbitrary <CustomType>]` and `[ManualShrinking <CustomType>]`.
Let us look at an example.
First we define an instance for the typeclass Arbitrary with the type Pt:
```haskell
instance : Arbitrary Pt where
  generate g :=
    let (x, g1) := (Arbitrary.generate (α:=Int) g)
    let (y, g2) := (Arbitrary.generate (α:=Int) g1)
    (⟨x, y⟩, g2)
```
Then we define an instance for the typeclass ManualShrinking with the Pt:
```haskell
def shrinkPt (p : Pt) (prop : Pt → Bool) (map : Pt → Pt) : Option Pt :=
  let cur := map p
  if prop cur then none
  else
    let c1 := map { p with y := 0 }
    let c2 := map { p with x := 0 }
    if ¬ prop c1 ∧ (Int.natAbs c1.x + Int.natAbs c1.y)
                  ≤ (Int.natAbs cur.x + Int.natAbs cur.y)
    then some c1
    else if ¬ prop c2 ∧ (Int.natAbs c2.x + Int.natAbs c2.y)
                       ≤ (Int.natAbs cur.x + Int.natAbs cur.y)
    then some c2
    else some cur
    
instance : ManualShrinking Pt where
  shrink p prop map := shrinkPt p prop map    
```
Now when we define a property using `Pt` we can just pass the property to `leanCheck` and Lean's instance search will automatically find the corresponding implementation just like for the basic types. For more details you can take a look at the examples in `Leancheck\examples\Examples.lean` and `Leancheck\examples\CustomStructureExample.lean`. Both can also be executed by running the commands `lake exe Examples prop`, `lake exe Examples lambda`, `lake exe Examples --` or `lake exe CustomStructureExample`.
All the tests are in `Leancheck\tests\Tests.lean` can be executed by running the command `lake test`.


## About the Development Process

The overall scope of the project has been known from the beginning. Challenges mainly occured with the usage of Lean specific concepts, which are rather unusual to comparable languages like Haskell. To name some examples:

- There have been numerous times, where the function `leancheck` has been reimplemented and refactored, and since Lean demands a termination proof for recursive calls, the function was at times `partial` since the proof was impossible. This has been since then remedied by defining recursive loops

- Using `lake test` was quite unclear, since there have been no comparable test libraries on Reservoir at the start of development

- In general, knowledge about other programming languages and paradigms have not been compatible with Lean's way of programming. 

## Ressources

- Base project: https://hackage.haskell.org/package/QuickCheck

- QuickCheck manual: https://www.cse.chalmers.se/~rjmh/QuickCheck/manual.html 

- Lean references: https://lean-lang.org/learn/
