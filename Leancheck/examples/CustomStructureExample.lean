/-
  This is a file containing an example with the library using a custom structure
  Either execute `lake exe CustomStructureExample` for a comprehensive view or look into the source file
-/

import Std
import Leancheck

open Std

def expect (ok : Bool) (msg : String) : IO Unit :=
  if ok then pure () else throw <| IO.userError msg

def expectSome {α} (msg : String) : Option α → IO α
| some v => pure v
| none   => throw <| IO.userError msg

def g0 : StdGen := mkStdGen 12345

structure Pt where
  x : Int
  y : Int
deriving Repr, BEq

instance : ToString Pt where
  toString p := s!"Pt({p.x},{p.y})"

def genPt : StdGen → Pt × StdGen := fun g =>
  let (x, g1) := (Arbitrary.generate (α:=Int) g)
  let (y, g2) := (Arbitrary.generate (α:=Int) g1)
  (⟨x, y⟩, g2)

def genPtTriple : StdGen → ((Pt × Pt × Pt) × StdGen) := fun g =>
  let (a, g1) := genPt g
  let (b, g2) := genPt g1
  let (c, g3) := genPt g2
  ((a, b, c), g3)

def l1 (p : Pt) : Nat := (Int.natAbs p.x) + (Int.natAbs p.y)

instance : Arbitrary Pt where
  generate g :=
    let (x, g1) := (Arbitrary.generate (α:=Int) g)
    let (y, g2) := (Arbitrary.generate (α:=Int) g1)
    (⟨x, y⟩, g2)

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

def shrinkPtTriple
  (t    : Pt × Pt × Pt)
  (prop : (Pt × Pt × Pt) → Bool)
  (map  : (Pt × Pt × Pt) → (Pt × Pt × Pt))
  : Option (Pt × Pt × Pt) :=
  let (a, bc) := t
  let (b, c)  := bc
  let y0      := map (a, b, c)
  let ya0     := y0.fst
  let ybc0    := y0.snd
  let yb0     := ybc0.fst
  let yc0     := ybc0.snd
  if prop y0 then
    none
  else
    let propA : Pt → Bool := fun aM => prop (aM, (yb0, yc0))
    let mapA  : Pt → Pt   := fun aU => (map (aU, (b,  c))).fst
    let a'    := (shrinkPt a propA mapA).getD ya0
    let candA := (a', (yb0, yc0))
    if ¬ prop candA then
      some candA
    else
      let propB : Pt → Bool := fun bM => prop (ya0, (bM, yc0))
      let mapB  : Pt → Pt   := fun bU => (map (a,  (bU, c ))).snd.fst
      let b'    := (shrinkPt b propB mapB).getD yb0
      let candB := (ya0, (b', yc0))
      if ¬ prop candB then
        some candB
      else
        let propC : Pt → Bool := fun cM => prop (ya0, (yb0, cM))
        let mapC  : Pt → Pt   := fun cU => (map (a,  (b,  cU))).snd.snd
        let c'    := (shrinkPt c propC mapC).getD yc0
        let candC := (ya0, (yb0, c'))
        if ¬ prop candC then some candC else some y0

instance : ManualShrinking Pt where
  shrink p prop map := shrinkPt p prop map

instance : ManualShrinking (Pt × Pt × Pt) where
  shrink t prop map := shrinkPtTriple t prop map

def manhattan (p q : Pt) : Nat :=
  (Int.natAbs (p.x - q.x)) + (Int.natAbs (p.y - q.y))

def imin (a b : Int) : Int := if a ≤ b then a else b
def imax (a b : Int) : Int := if a ≥ b then a else b

def med3Int (a b c : Int) : Int :=
  let mx := imax (imax a b) c
  let mn := imin (imin a b) c
  a + b + c - mx - mn

def medPt (a b c : Pt) : Pt :=
  { x := med3Int a.x b.x c.x
  , y := med3Int a.y b.y c.y }

def sumDistToTriple (p a b c : Pt) : Nat :=
  manhattan p a + manhattan p b + manhattan p c

def sizeTriple (t : Pt × Pt × Pt) : Nat :=
  let (a,b,c) := t
  (Int.natAbs a.x + Int.natAbs a.y)
+ (Int.natAbs b.x + Int.natAbs b.y)
+ (Int.natAbs c.x + Int.natAbs c.y)

def prop_L1MedianOptimal (t : Pt × Pt × Pt) : Bool :=
  let (a, b, c) := t
  let m  := medPt a b c
  let sm := sumDistToTriple m a b c
  let sa := sumDistToTriple a a b c
  let sb := sumDistToTriple b a b c
  let sc := sumDistToTriple c a b c
  decide (sm ≤ Nat.min sa (Nat.min sb sc))

def prop_triangleEqualityWrong (t : Pt × Pt × Pt) : Bool :=
  let (a, b, c) := t
  manhattan a c == manhattan a b + manhattan b c

def main (_ : List String) : IO Unit := do
  leanCheck (α := Pt × Pt × Pt)
    "A"
    prop_L1MedianOptimal
    id
    genPtTriple
    shrinkPtTriple
    100
    12345

  leanCheck (α := Pt × Pt × Pt)
    "B"
    prop_triangleEqualityWrong
    id
    genPtTriple
    shrinkPtTriple
    200
    12345
