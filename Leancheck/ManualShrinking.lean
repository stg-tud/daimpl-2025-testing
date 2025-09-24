def shrinkNat (x : Nat) (prop : Nat → Bool) (map : Nat → Nat) : Option Nat :=
  let rec loop : Nat → Option Nat → Option Nat
    | 0, best =>
      let y0 := map 0
      let best := if ¬ prop y0 ∧ (y0 < best.getD x) then some y0 else best
      best
    | (n+1), best =>
      let y := map (n+1)
      let best := if ¬ prop y ∧ (y < best.getD x) then some y else best
      loop n best
  loop x none

def shrinkInt (x : Int) (prop : Int → Bool) (map : Int → Int) : Option Int :=
  let s : Int := if x ≥ 0 then (1 : Int) else (-1)
  let rec loop : Nat → Option Int → Option Int
    | 0, best =>
      let y0 := map 0
      let best := if ¬ prop y0 ∧ (Int.natAbs y0 < Int.natAbs (best.getD x)) then some y0 else best
      best
    | (k+1), best =>
      let cand : Int := s * Int.ofNat (k+1)
      let y := map cand
      let best := if ¬ prop y ∧ (Int.natAbs y < Int.natAbs (best.getD x)) then some y else best
      loop k best
  loop (Int.natAbs x) none

partial def shrinkList {α : Type}
  (xs : List α)
  (prop : List α → Bool)
  (map : List α → List α) : Option (List α) :=

  let yx := map xs
  if prop yx then
    none
  else
    let rec loop (cur : List α) : List α :=
      let yc := map cur
      let n  := cur.length
      if n ≤ 1 then
        yc
      else
        let k     := n / 2
        let left  := cur.take k
        let right := cur.drop k
        let yL    := map left
        if ¬ prop yL then
          loop left
        else
          let yR := map right
          if ¬ prop yR then
            loop right
          else
            yc
    some (loop xs)

partial def shrinkArray {α : Type}
  (xs : Array α)
  (prop : Array α → Bool)
  (map : Array α → Array α) : Option (Array α) :=

  let yx := map xs
  if prop yx then
    none
  else
    let rec loop (cur : Array α) : Array α :=
      let yc := map cur
      let n  := cur.size
      if n ≤ 1 then
        yc
      else
        let k     := n / 2
        let left  := cur.extract 0 k
        let right := cur.extract k n
        let yL    := map left
        if ¬ prop yL then
          loop left
        else
          let yR := map right
          if ¬ prop yR then
            loop right
          else
            yc
    some (loop xs)

def shrinkOption {α : Type}
  (x : Option α)
  (prop : Option α → Bool)
  (map : Option α → Option α) : Option (Option α) :=

  let y0 := map x
  if prop y0 then
    none
  else
    match x with
    | none =>
        none
    | some _ =>
        let yNone := map none
        if ¬ prop yNone then
          some yNone
        else
          some y0

def shrinkPair {α β : Type}
  (shrA : α → (α → Bool) → (α → α) → Option α)
  (shrB : β → (β → Bool) → (β → β) → Option β)
  (p : α × β)
  (prop : (α × β) → Bool)
  (map : (α × β) → (α × β)) : α × β :=

  let (a, b) := p
  let y0 := map (a, b)
  let ya0 := y0.fst
  let yb0 := y0.snd

  let propA : α → Bool := fun a' => prop (a', yb0)
  let mapA : α → α := fun a' => (map (a', b)).fst
  let a' := (shrA a propA mapA).getD ya0
  let candA := (a', yb0)
  if ¬ prop candA then
    candA
  else
    let propB : β → Bool := fun b' => prop (ya0, b')
    let mapB : β → β    := fun b' => (map (a, b')).snd
    let b' := (shrB b propB mapB).getD yb0
    let candB := (ya0, b')
    if ¬ prop candB then candB else y0


class ManualShrinking (α : Type) where
  shrink : α → (prop : α → Bool) → (map : α → α) → Option α

instance : ManualShrinking Bool where
  shrink n _ _ := n

instance : ManualShrinking Nat where
  shrink n prop map := shrinkNat n prop map

instance : ManualShrinking Int where
  shrink n prop map := shrinkInt n prop map

instance {α : Type} [ManualShrinking α] : ManualShrinking (List α) where
  shrink n prop map := shrinkList n prop map

instance {α : Type} [ManualShrinking α] : ManualShrinking (Array α) where
  shrink n prop map := shrinkArray n prop map

instance {α β : Type} [ManualShrinking α] [ManualShrinking β]
  : ManualShrinking (α × β) where
  shrink p prop map :=
    shrinkPair
      ManualShrinking.shrink
      ManualShrinking.shrink
      p prop map
