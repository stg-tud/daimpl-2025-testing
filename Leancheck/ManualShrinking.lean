def shrinkNat (x : Nat) (prop : Nat → Bool) (map : Nat → Nat) : Nat :=
  let rec loop : Nat → Option Nat → Nat
    | 0, best =>
      let y0 := map 0
      let best := if ¬ prop y0 ∧ (y0 < best.getD x) then some y0 else best
      best.getD x
    | (n+1), best =>
      let y := map (n+1)
      let best := if ¬ prop y ∧ (y < best.getD x) then some y else best
      loop n best
  loop x (map x)

def shrinkInt (x : Int) (prop : Int → Bool) (map : Int → Int) : Int :=
  let s : Int := if x ≥ 0 then (1 : Int) else (-1)
  let rec loop : Nat → Int → Int
    | 0, best =>
      let y0 := map 0
      let best := if ¬ prop y0 ∧ (Int.natAbs y0 < Int.natAbs best) then y0 else best
      best
    | (k+1), best =>
      let cand : Int := s * Int.ofNat (k+1)
      let y := map cand
      let best := if ¬ prop y ∧ (Int.natAbs y < Int.natAbs best) then y else best
      loop k best
  loop (Int.natAbs x) (map x)

def shrinkPair {α β : Type}
  (shrA : α → (α → Bool) → (α → α) → α)
  (shrB : β → (β → Bool) → (β → β) → β)
  (p : α × β)
  (prop : (α × β) → Bool)
  (map  : (α × β) → (α × β)) : α × β :=
  let (a, b) := p

  let propA : α → Bool := fun a' => prop (map (a', b))
  let mapA  : α → α    := fun a' => (map (a', b)).fst
  let a' := shrA a propA mapA
  let candA := (a', b)
  let y := (map candA)
  if ¬ prop y then
    y
  else
    let propB : β → Bool := fun b' => prop (map (a, b'))
    let mapB  : β → β    := fun b' => (map (a, b')).snd
    let b' := shrB b propB mapB
    let candB := (a, b')
    let y := (map candB)
    if ¬ prop y then y else p


class ManualShrinking (α : Type) where
  shrink : α → (prop : α → Bool) → (map : α → α) → α

instance : ManualShrinking Bool where
  shrink n _ _ := n

instance : ManualShrinking Nat where
  shrink n prop map := shrinkNat n prop map

instance : ManualShrinking Int where
  shrink n prop map := shrinkInt n prop map

instance {α β : Type} [ManualShrinking α] [ManualShrinking β]
  : ManualShrinking (α × β) where
  shrink p prop map :=
    shrinkPair
      ManualShrinking.shrink
      ManualShrinking.shrink
      p prop map
