def shrink {α : Type} (x : α) : α :=
  x

def shrinkNat (x: Nat) : Nat :=
  if x == 0 then 0 else 1

def shrinkInt (x : Int) : Int :=
  x.sign

def shrinkFloat (x : Float) : Float :=
  if x == 0.0 then 0.0 else if x > 0.0 then 0.1 else -0.1

def shrinkList {α : Type} (shrinker : α → α) (xs : List α) : List α :=
  xs

class Shrinking (α : Type) where
  shrink : α → α

instance : Shrinking Bool where
  shrink n := n

instance : Shrinking Nat where
  shrink n := shrinkNat n

instance : Shrinking Int where
  shrink n := shrinkInt n

instance : Shrinking Float where
  shrink n := shrinkFloat n

instance {α : Type} [Shrinking α] : Shrinking (List α) where
  shrink xs := shrinkList Shrinking.shrink xs
/-
instance {α : Type} [Shrinking α] : Shrinking (Array α) where
  shrink g := randArray Arbitrary.generate g

instance {α : Type} [Shrinking α] : Shrinking (Option α) where
  shrink g := randOptional Arbitrary.generate g
-/
