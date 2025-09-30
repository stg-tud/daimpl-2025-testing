/-
  This is a file containing some basic tests with the library
  Either execute `lake test` for a comprehensive view or look into the source file
-/

import Std
import Leancheck

open Std

def expect (ok : Bool) (msg : String) : IO Unit :=
  if ok then pure () else throw <| IO.userError msg

def expectSome {α} (msg : String) : Option α → IO α
| some v => pure v
| none   => throw <| IO.userError msg


def g0 : StdGen :=  mkStdGen 12345

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

def prop_boolFalse (x : Bool) : Bool :=
  x == True

def prop_boolTrue (x : Bool) : Bool :=
  x == x

def prop_natFalse (x : Nat) : Bool :=
  x == 1

def prop_natTrue (x : Nat) : Bool :=
  x == x

def prop_intFalse (x : Int) : Bool :=
  x == 1

def prop_intTrue (x : Int) : Bool :=
  x == x

def prop_listFalse (x : List Int) : Bool :=
  x == List.reverse x

def prop_listTrue (x : List Int) : Bool :=
  x == List.reverse (List.reverse x)

def prop_arrayFalse (x : Array Int) : Bool :=
  x == Array.reverse x

def prop_arrayTrue (x : Array Int) : Bool :=
  x == Array.reverse (Array.reverse x)

def prop_pairFalse (x : (Int × Int)) : Bool :=
  let (a, b) := x
  (a, b) == (b, a)

def prop_pairTrue (x : (Int × Int)) : Bool :=
  x == x

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

def checkFail {α}
  (name   : String)
  (prop   : α → Bool)
  (out    : TestOutput α)
  (noWorse : α → α → Bool := fun _ _ => True)
  [ToString α]
: IO Unit := do
  expect (out.ex.isSome) s!"[{name}] expected a counterexample"
  expect (out.iter < out.trial) s!"[{name}] should stop early on failure"
  let ex ← expectSome s!"[{name}] missing ex" out.ex
  expect (¬ prop ex) s!"[{name}] ex must falsify prop; got {toString ex}"
  match out.shrink with
  | none => pure ()
  | some s =>
    expect (¬ prop s) s!"[{name}] shrink should still falsify; got {toString s}"
    expect (noWorse s ex) s!"[{name}] shrink should not be worse"

def checkPass {α}
  (name : String)
  (out  : TestOutput α)
  (expectedTrials : Nat := 100)
: IO Unit := do
  expect (out.ex.isNone) s!"[{name}] unexpected counterexample"
  expect (out.shrink.isNone) s!"[{name}] shrink should be none when no failure"
  expect (out.iter == out.trial) s!"[{name}] expected to consume all trials"
  expect (out.trial == expectedTrials) s!"[{name}] wrong trial count"

def maxAbsList (xs : List Int) : Nat :=
  xs.foldl (fun acc x => Nat.max acc (Int.natAbs x)) 0

def maxAbsArray (xs : Array Int) : Nat :=
  xs.foldl (fun acc x => Nat.max acc (Int.natAbs x)) 0

def noWorseListMaxAbsLen (s e : List Int) : Bool :=
  s.length ≤ e.length && maxAbsList s ≤ maxAbsList e

def noWorseArrayMaxAbsLen (s e : Array Int) : Bool :=
  s.size ≤ e.size && maxAbsArray s ≤ maxAbsArray e

def noWorsePairInt (s e : Int × Int) : Bool :=
  (Int.natAbs s.fst ≤ Int.natAbs e.fst) && (Int.natAbs s.snd ≤ Int.natAbs e.snd)

def main : IO Unit := do
  let outBoolFalse :=
    leanCheckCore
      prop_boolFalse
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkFail "prop bool false" prop_boolFalse outBoolFalse (fun shr ex => shr ≤ ex)

  let outBoolTrue :=
    leanCheckCore
      prop_boolTrue
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkPass "prop bool true" outBoolTrue 100

  let outNatFalse :=
    leanCheckCore
      prop_natFalse
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkFail "prop nat false" prop_natFalse outNatFalse (fun shr ex => shr ≤ ex)

  let outNatTrue :=
    leanCheckCore
      prop_natTrue
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkPass "prop nat true" outNatTrue 100

  let outNatEvenFalse :=
    leanCheckCore
      prop_natFalse
      (fun x => x * 2)
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkFail "prop nat false" prop_natFalse outNatEvenFalse (fun shr ex => shr ≤ ex && shr % 2 == 0 && ex % 2 == 0)

  let outNatEvenTrue :=
    leanCheckCore
      prop_natTrue
      (fun x => x * 2)
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkPass "prop nat true" outNatEvenTrue 100
  let outIntFalse :=
    leanCheckCore
      prop_intFalse
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkFail "prop int false" prop_intFalse outIntFalse (fun shr ex => Int.natAbs shr ≤ Int.natAbs ex)

  let outIntTrue :=
    leanCheckCore
      prop_intTrue
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkPass "prop int true" outIntTrue 100

  let outListFalse :=
    leanCheckCore
      prop_listFalse
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkFail "prop list false" prop_listFalse outListFalse (noWorseListMaxAbsLen)

  let outListTrue :=
    leanCheckCore
      prop_listTrue
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkPass "prop list true" outListTrue 100

  let outArrayFalse :=
    leanCheckCore
      prop_arrayFalse
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkFail "prop array false" prop_arrayFalse outArrayFalse (noWorseArrayMaxAbsLen)

  let outArrayTrue :=
    leanCheckCore
      prop_arrayTrue
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkPass "prop array true" outArrayTrue 100

  let outPairFalse :=
    leanCheckCore (α := Int × Int)
      prop_pairFalse
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkFail "prop pair false" prop_pairFalse outPairFalse (noWorse := noWorsePairInt)

  let outPairTrue :=
    leanCheckCore (α := Int × Int)
      prop_pairTrue
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkPass "prop pair true" outPairTrue 100


  let outA :=
    leanCheckCore
      prop_L1MedianOptimal
      id
      genPtTriple
      shrinkPtTriple
      g0
      200

  checkPass "prop l1 median optimal" outA 200

  let outB :=
  leanCheckCore
    prop_triangleEqualityWrong
    id
    genPtTriple
    shrinkPtTriple
    g0
    200

  checkFail "prop triangle equality wrong" prop_triangleEqualityWrong outB (fun shr ex => sizeTriple shr ≤ sizeTriple ex)


  IO.println "Tests: OK"
