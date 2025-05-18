import Std

open Std

def randIntInRange (g : StdGen) (lo hi : Int) : Int × StdGen :=
  let (n, g') := randNat g (lo.toNat) (hi.toNat)
  (Int.ofNat n, g')

def randIntList (g : StdGen) (len : Nat) (lo hi : Int) : List Int × StdGen :=
  match len with
  | 0 => ([], g)
  | n + 1 =>
    let (x, g1) := randIntInRange g lo hi
    let (xs, g2) := randIntList g1 n lo hi
    (x :: xs, g2)

def randIntListIteratively (g : StdGen) (len : Nat) (lo hi : Int) : List Int × StdGen := Id.run do
  let mut g := g
  let mut lst := []
  for _ in [0:len] do
    let (x, g') := randIntInRange g lo hi
    lst := x :: lst -- append element to beginning bc of performance
    g := g'
  (lst, g)

def leanCheck (prop : Int → Bool) : IO Unit := do
  let mut failed : Bool := false
  let g := mkStdGen
  let (lst, _) := randIntListIteratively g 100 0 100
  for x in lst do
    if ¬ prop x then
      failed := true
      IO.println s!"Failed on {x}"

  if ¬ failed then
    IO.println "Ok, passed 100 tests."
