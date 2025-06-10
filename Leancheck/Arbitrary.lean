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

def randomFloat (g : StdGen) : Float × StdGen :=
  let (n, g') := randNat g 0 (2 ^ 64)
  let floatVal : Float := n.toFloat / (2 ^ 64).toFloat
  (floatVal, g')

-- without tail recursion
/-
def randList {α : Type} (gen : StdGen → α × StdGen) (g : StdGen) : List α × StdGen :=
    let (len, g) := randNatInRange g 0 10
    let rec aux : (n : Nat) → (g : StdGen) → List α × StdGen
      | 0, g => ([], g)
      | n + 1, g =>
        let (x, g1) := gen g
        let (xs, g2) := aux n g1
        (x :: xs, g2)
    aux len g
-/

-- with tail recursion
def randList {α : Type} (gen : StdGen → α × StdGen) (g : StdGen) : List α × StdGen :=
  let (len, g') := randNat g 0 10
  let rec loop (n : Nat) (acc : List α) (g : StdGen) : List α × StdGen :=
    match n with
    | 0 => (acc, g)
    | n + 1 =>
      let (x, g'') := gen g
      loop n (x :: acc) g''
  loop len [] g'

def randArray {α : Type} (gen : StdGen → α × StdGen) (g : StdGen) : Array α × StdGen :=
  let (len, g') := randNat g 0 10
  let rec loop (n : Nat) (acc : Array α) (g : StdGen) : Array α × StdGen :=
    match n with
    | 0 => (acc, g)
    | n + 1 =>
      let (x, g'') := gen g
      loop n (acc.push x) g''
  loop len #[] g'

def randOptional {α : Type} (gen : StdGen → α × StdGen) (g : StdGen) : Option α × StdGen :=
  let (b, g') := randBool g
  if b then
    let (x, g'') := gen g'
    (some x, g'')
  else
    (none, g')


class Arbitrary (α : Type) where
  generate : StdGen → α × StdGen

instance : Arbitrary Bool where
  generate g := randBool g

instance : Arbitrary Nat where
  generate g := randNat g 0 100

instance : Arbitrary Int where
  generate g := randIntInRange g (-100) 100

instance : Arbitrary Float where
  generate g := randomFloat g

instance {α : Type} [Arbitrary α] : Arbitrary (List α) where
  generate g := randList Arbitrary.generate g

instance {α : Type} [Arbitrary α] : Arbitrary (Array α) where
  generate g := randArray Arbitrary.generate g

instance {α : Type} [Arbitrary α] : Arbitrary (Option α) where
  generate g := randOptional Arbitrary.generate g
