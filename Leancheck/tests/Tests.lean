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

def prop_bool_false (x : Bool) : Bool :=
  x == True

def prop_bool_true (x : Bool) : Bool :=
  x == x

def prop_nat_false (x : Nat) : Bool :=
  x == 1

def prop_nat_true (x : Nat) : Bool :=
  x == x

def prop_int_false (x : Int) : Bool :=
  x == 1

def prop_int_true (x : Int) : Bool :=
  x == x

def prop_list_false (x : List Int) : Bool :=
  x == List.reverse x

def prop_list_true (x : List Int) : Bool :=
  x == List.reverse (List.reverse x)

def prop_array_false (x : Array Int) : Bool :=
  x == Array.reverse x

def prop_array_true (x : Array Int) : Bool :=
  x == Array.reverse (Array.reverse x)

def prop_pair_false (x : (Int × Int)) : Bool :=
  let (a, b) := x
  (a, b) == (b, a)

def prop_pair_true (x : (Int × Int)) : Bool :=
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

def main (_ : List String) : IO Unit := do
  let outBoolFalse :=
    leanCheckCore
      prop_bool_false
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkFail "prop_bool_false" prop_bool_false outBoolFalse (fun shr ex => shr ≤ ex)

  let outBoolTrue :=
    leanCheckCore
      prop_bool_true
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkPass "prop_bool_true" outBoolTrue 100

  let outNatFalse :=
    leanCheckCore
      prop_nat_false
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkFail "prop_nat_false" prop_nat_false outNatFalse (fun shr ex => shr ≤ ex)

  let outNatTrue :=
    leanCheckCore
      prop_nat_true
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkPass "prop_nat_true" outNatTrue 100

  let outIntFalse :=
    leanCheckCore
      prop_int_false
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkFail "prop_int_false" prop_int_false outIntFalse (fun shr ex => Int.natAbs shr ≤ Int.natAbs ex)

  let outIntTrue :=
    leanCheckCore
      prop_int_true
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkPass "prop_int_true" outIntTrue 100

  let outListFalse :=
    leanCheckCore
      prop_list_false
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkFail "prop_list_false" prop_list_false outListFalse (noWorseListMaxAbsLen)

  let outListTrue :=
    leanCheckCore
      prop_list_true
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkPass "prop_list_true" outListTrue 100

  let outArrayFalse :=
    leanCheckCore
      prop_array_false
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkFail "prop_array_false" prop_array_false outArrayFalse (noWorseArrayMaxAbsLen)

  let outArrayTrue :=
    leanCheckCore
      prop_array_true
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkPass "prop_array_true" outArrayTrue 100

  let outPairFalse :=
    leanCheckCore (α := Int × Int)
      prop_pair_false
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkFail "prop_pair_false" prop_pair_false outPairFalse (noWorse := noWorsePairInt)

  let outPairTrue :=
    leanCheckCore (α := Int × Int)
      prop_pair_true
      id
      Arbitrary.generate
      ManualShrinking.shrink
      g0
      100

  checkPass "prop_pair_true" outPairTrue 100


  let outA :=
    leanCheckCore (α := Pt × Pt × Pt)
      prop_L1MedianOptimal
      id
      genPtTriple
      shrinkPtTriple
      g0
      100

  expect (outA.ex.isNone) "[A] L1-median: unexpected counterexample"
  expect (outA.shrink.isNone) "[A] L1-median: shrink should be none when no failure"
  expect (outA.iter == outA.trial) "[A] L1-median: expected to consume all trials"

  expect (outA.trial == 100) "[A] L1-median: wrong trial count"

  expect (outA.ex == none) "[A] L1-median: ex must be none on success"
  expect (outA.shrink == none) "[A] L1-median: shrink must be none on success"

  let outB :=
  leanCheckCore (α := Pt × Pt × Pt)
    prop_triangleEqualityWrong
    id
    genPtTriple
    shrinkPtTriple
    g0
    200

  expect (outB.ex.isSome) "[B] expected a counterexample"
  expect (outB.iter < outB.trial) "[B] should stop early on failure"
  expect (outB.ex.isSome) "[B] expected a counterexample"
  let exVal ← expectSome "[B] missing ex" outB.ex
  expect (¬ prop_triangleEqualityWrong exVal) "[B] ex must falsify prop"

  match outB.shrink with
  | none => pure ()
  | some s =>
    expect (¬ prop_triangleEqualityWrong s) "[B] shrink should still falsify"
    expect (sizeTriple s ≤ sizeTriple exVal) "[B] shrink should not increase size"

  IO.println "Custom Pt generator/shrinker integration: OK"
