/--
Generates a random `Nat` in the interval `[lo, hi]` using the given `StdGen`.

Returns a pair `(x, g')` where:
- `x` is the random integer in the desired range
- `g'` is the updated random generator
-/
def randNatInRange (g : StdGen) (lo hi : Int) : Nat × StdGen :=
  let (n, g') : Nat × StdGen := randNat g (lo.toNat) (hi.toNat)
  (n, g')

/--
Generates a random `Int` in the interval `[lo, hi]` using the given `StdGen`.

Returns a pair `(x, g')` where:
- `x` is the random natural in the desired range
- `g'` is the updated random generator
-/
def randIntInRange (g : StdGen) (lo hi : Int) : Int × StdGen :=
  if lo > hi then
    panic! s!"Invalid range: lo = {lo}, hi = {hi}"
  else
    let diff : Nat := (hi - lo).toNat
    let (n, g') : Nat × StdGen := randNat g 0 diff
    let n' : Int := n + lo
    (n', g')


class Arbitrary (α : Type) where
  generate : StdGen → α × StdGen

instance : Arbitrary Bool where
  generate g := randBool g

instance : Arbitrary Nat where
  generate g := randNatInRange g 0 100

instance : Arbitrary Int where
  generate g := randIntInRange g (-100) 100

instance {α : Type} [Arbitrary α] : Arbitrary (List α) where
  generate g :=
    let (len, g) := randNatInRange g 0 10
    let rec gen : (n : Nat) → (g : StdGen) → List α × StdGen
      | 0, g => ([], g)
      | n + 1, g =>
        let (x, g1) := Arbitrary.generate g
        let (xs, g2) := gen n g1
        (x :: xs, g2)
    gen len g
