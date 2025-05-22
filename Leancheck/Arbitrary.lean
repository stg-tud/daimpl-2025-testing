/--
Generates a random `Nat` in the interval `[lo, hi]` using the given `StdGen`.

Returns a pair `(x, g')` where:
- `x` is the random integer in the desired range
- `g'` is the updated random generator
-/
def randNatInRange (g : StdGen) (lo hi : Int) : Nat × StdGen :=
  let (n, g') := randNat g (lo.toNat) (hi.toNat)
  (n, g')

/--
Generates a random `Int` in the interval `[lo, hi]` using the given `StdGen`.

Returns a pair `(x, g')` where:
- `x` is the random natural in the desired range
- `g'` is the updated random generator
-/
def randIntInRange (g : StdGen) (lo hi : Int) : Int × StdGen :=
  let (n, g') := randNat g (lo.toNat) (hi.toNat)
  (Int.ofNat n, g')


class Arbitrary (α : Type) where
  generate : StdGen → α × StdGen

instance : Arbitrary Bool where
  generate g := randBool g

instance : Arbitrary Nat where
  generate g := randNatInRange g 0 100

instance : Arbitrary Int where
  generate g := randIntInRange g 0 100

instance {α : Type} [Arbitrary α] : Arbitrary (List α) where
  generate g := Id.run do
    let mut g := g
    let mut lst := []
    let (len, _) := randNatInRange g 0 10
    for _ in [0:len] do
      let (x, g') := Arbitrary.generate g
      lst := x :: lst -- append element to beginning bc of performance
      g := g'
    (lst, g)
