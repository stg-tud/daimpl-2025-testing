def shrink {α : Type} (x : α) : α :=
  x

def shrinkNat (x: Nat) : Nat :=
  if x == 0 then 0 else 1

def shrinkInt (x : Int) : Int :=
  x.sign

def shrinkFloat (x : Float) : Float :=
  if x == 0.0 then 0.0 else if x > 0.0 then 0.1 else -0.1

def shrinkList {α : Type} (shrinker : α → α) (xs : List α) : List α :=
  (xs.take 2).map shrinker

def shrinkArray {α : Type} (shrinker : α → α) (xs : Array α) : Array α :=
  ((xs.toList.take 2).map shrinker).toArray

def shrinkOptional {α : Type} (shrinker : α → α) (n : Option α) : Option α :=
  n.map shrinker

def shrinkPair {α β : Type} (shrinkerA : α → α) (shrinkerB : β → β) (n : α × β) : (α × β):=
  let (a, b) := n
  (shrinkerA a, shrinkerB b)


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

instance {α : Type} [Shrinking α] : Shrinking (Array α) where
  shrink xs := shrinkArray Shrinking.shrink xs

instance {α : Type} [Shrinking α] : Shrinking (Option α) where
  shrink n := shrinkOptional Shrinking.shrink n

instance {α β : Type} [Shrinking α] [Shrinking β] : Shrinking (α × β) where
  shrink n := shrinkPair Shrinking.shrink Shrinking.shrink n
