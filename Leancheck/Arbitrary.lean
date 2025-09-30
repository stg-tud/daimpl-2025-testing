/--
Generates a random `Int` in the interval `[lo, hi]` using the given `StdGen`.

Returns a pair `(x, g')` where:
- `x` is the random integer in the desired range
- `g'` is the updated random generator
-/
def randIntInRange (g : StdGen) (lo hi : Int) : Int × StdGen :=
  let lo' := if lo ≤ hi then lo else hi
  let hi' := if lo ≤ hi then hi else lo
  let diff : Nat := (hi' - lo').toNat
  let (n, g') : Nat × StdGen := randNat g 0 diff
  let n' : Int := n + lo'
  (n', g')

/--
Generates a random `List α` using the given element generator `gen` and `StdGen`.

- First draws a length `len ∈ [0, 10]`.
- Then produces `len` elements by repeatedly calling `gen`, threading the RNG.
Returns `(xs, g')`.
-/
def randList {α : Type} (gen : StdGen → α × StdGen) (g : StdGen) : List α × StdGen :=
  let (len, g') := randNat g 0 10
  let rec loop (n : Nat) (acc : List α) (g : StdGen) : List α × StdGen :=
    match n with
    | 0 => (acc, g)
    | n + 1 =>
      let (x, g'') := gen g
      loop n (x :: acc) g''
  loop len [] g'

/--
Generates a random `Array α` using the given element generator `gen` and `StdGen`.

- First draws a length `len ∈ [0, 10]`.
- Then produces `len` elements by repeatedly calling `gen`, threading the RNG.
Returns `(arr, g')`.
-/
def randArray {α : Type} (gen : StdGen → α × StdGen) (g : StdGen) : Array α × StdGen :=
  let (len, g') := randNat g 0 10
  let rec loop (n : Nat) (acc : Array α) (g : StdGen) : Array α × StdGen :=
    match n with
    | 0 => (acc, g)
    | n + 1 =>
      let (x, g'') := gen g
      loop n (acc.push x) g''
  loop len #[] g'

/--
Generates a random `Option α` using the given element generator `gen` and `StdGen`.

- Flips a random boolean; if `true`, generates `some x` via `gen`, else `none`.
Returns `(opt, g')`.
-/
def randOptional {α : Type} (gen : StdGen → α × StdGen) (g : StdGen) : Option α × StdGen :=
  let (b, g') := randBool g
  if b then
    let (x, g'') := gen g'
    (some x, g'')
  else
    (none, g')

/--
Generates a random pair `(α × β)` using element generators `genA`, `genB` and `StdGen`.

- Draws `a` with `genA`, then `b` with `genB`, threading the RNG.
Returns `((a, b), g')`.
-/
def randPair {α β : Type} (genA : StdGen → α × StdGen) (genB : StdGen → β × StdGen) (g : StdGen) : (α × β) × StdGen :=
  let (a, g1) := genA g
  let (b, g2) := genB g1
  ((a, b), g2)


class Arbitrary (α : Type) where
  generate : StdGen → α × StdGen

instance : Arbitrary Bool where
  generate g := randBool g

instance : Arbitrary Nat where
  generate g := randNat g 0 100

instance : Arbitrary Int where
  generate g := randIntInRange g (-100) 100

instance {α : Type} [Arbitrary α] : Arbitrary (List α) where
  generate g := randList Arbitrary.generate g

instance {α : Type} [Arbitrary α] : Arbitrary (Array α) where
  generate g := randArray Arbitrary.generate g

instance {α : Type} [Arbitrary α] : Arbitrary (Option α) where
  generate g := randOptional Arbitrary.generate g

instance {α β : Type} [Arbitrary α] [Arbitrary β] : Arbitrary (α × β) where
  generate g := randPair Arbitrary.generate Arbitrary.generate g
