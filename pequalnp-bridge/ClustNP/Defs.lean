import PEqualNP.Library.SearchHelpers.TwoSatCPT
import PEqualNP.Library.SearchHelpers.TableauStepWLoop
import PEqualNP.Library.SearchHelpers.SearchToDecision
import RadiusClustering.PEqualNP.Clust

/-!
# A verifier for CLUST, as string functions

Built in pequalnp's style (`SatVerifierDefs.lean`): small named total functions on bit strings.
Strings are read in pairs: `[true, d]` a digit, `[false, true]` the end of a number,
`[false, false]` the end of a row. An instance is `encInst k τ M`; the witness `w` is a bit
string, `w[s] = true` meaning that point `s` is a centre. Plan: `docs/pequalnp.md`.
-/

namespace ClustNP

open PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.S2D (incB dig)

/-! ### Comparison of two numbers -/

/-- `leP A B acc` compares the numbers coded at the front of `A` and `B`, least significant digit
first; `acc` is the answer if all digits so far are equal. -/
def leP : List Bool → List Bool → Bool → Bool
  | true :: x :: A, true :: y :: B, acc => leP A B (if x == y then acc else y)
  | true :: _, _, _ => false
  | _, true :: _, _ => true
  | _, _, acc => acc

/-- The first symbol as a flag. -/
def f1 (s : List Bool) : List Bool := if s.head? = some true then [true] else []

/-- One step of the comparison on the packed state `pairB A (pairB B F)`. -/
def leStep (s : List Bool) : List Bool :=
  sel (hd (unpairB s).1)
    (sel (hd (unpairB (unpairB s).2).1)
      (pairB [] (pairB [] (unpairB (unpairB s).2).2))
      (pairB [] (pairB [] [true])))
    (sel (hd (unpairB (unpairB s).2).1)
      (pairB [] (pairB [] []))
      (pairB (unpairB s).1.tail.tail (pairB (unpairB (unpairB s).2).1.tail.tail
        (sel (bflag (decide (f1 (unpairB s).1.tail = f1 (unpairB (unpairB s).2).1.tail)))
          (f1 (unpairB (unpairB s).2).1.tail) (unpairB (unpairB s).2).2))))

/-- `leF A B` is nonempty iff the number coded by `A` is at most the one coded by `B`. -/
def leF (A B : List Bool) : List Bool :=
  (unpairB (unpairB (leStep^[(A ++ B).length] (pairB A (pairB B [true])))).2).2

/-! ### Reading an instance -/

/-- One `true` per pair `[false, false]`: the number of rows. -/
def endsU : List Bool → List Bool
  | false :: false :: r => true :: endsU r
  | _ :: _ :: r => endsU r
  | _ => []

/-- Drop through the first pair `[false, false]`: drop one row. -/
def dropRow : List Bool → List Bool
  | false :: false :: r => r
  | _ :: _ :: r => dropRow r
  | _ => []

/-- One `true` per pair `[false, true]` before the first `[false, false]`: the length of the
first row. -/
def rowLenU : List Bool → List Bool
  | false :: false :: _ => []
  | false :: true :: r => true :: rowLenU r
  | _ :: _ :: r => rowLenU r
  | _ => []

/-- The rows of an instance: drop `k` and `τ`. -/
def rowsS (x : List Bool) : List Bool := dropI (dropI x)

/-- The code of `d(s, y)` for `s < y`, from `un s`, `un y` and the instance. -/
def entryS (us uy x : List Bool) : List Bool :=
  headI (dropI^[(List.tail^[(true :: us).length] uy).length] (dropRow^[us.length] (rowsS x)))

/-! ### Well-formedness -/

/-- Phases of the acceptor: inside `k`, inside `τ` (`C`: digits canonical so far, `D`: last digit
`false`), at a row boundary with no row open (`R`) or after a number (`O`), inside a number of a
row, rejected. -/
inductive Ph : Type
  | kC | kD | tC | tD | R | O | rC | rD | dead
  deriving DecidableEq

instance : Fintype Ph :=
  ⟨{.kC, .kD, .tC, .tD, .R, .O, .rC, .rD, .dead}, fun q => by cases q <;> simp⟩

/-- The phase after one pair. -/
def phD : Ph → Bool → Bool → Ph
  | .kC, true, d => if d then .kC else .kD
  | .kC, false, true => .tC
  | .kD, true, d => if d then .kC else .kD
  | .tC, true, d => if d then .tC else .tD
  | .tC, false, true => .R
  | .tD, true, d => if d then .tC else .tD
  | .R, true, d => if d then .rC else .rD
  | .R, false, true => .O
  | .R, false, false => .R
  | .O, true, d => if d then .rC else .rD
  | .O, false, true => .O
  | .O, false, false => .R
  | .rC, true, d => if d then .rC else .rD
  | .rC, false, true => .O
  | .rD, true, d => if d then .rC else .rD
  | _, _, _ => .dead

/-- The acceptor reads one symbol at a time, keeping the first symbol of a pair. -/
def wfD : Ph × Option Bool → Bool → Ph × Option Bool
  | (p, none), a => (p, some a)
  | (p, some a), b => (phD p a b, none)

/-- `x` is `encInst k τ M` for some `k`, `τ`, `M`. -/
def wfI (x : List Bool) : Bool := decide (x.foldl wfD (.kC, none) = (.R, none))

/-! ### The checks -/

/-- Row `i` has `n - 1 - i` entries, on `pairB (un i) x`. -/
def triRow (z : List Bool) : List Bool :=
  bflag (!decide (rowLenU (dropRow^[(unpairB z).1.length] (rowsS (unpairB z).2)) ++
    true :: (unpairB z).1 = endsU (unpairB z).2))

/-- Bad rows of `x` (empty when `M` is triangular). -/
def triBad (x : List Bool) : List Bool :=
  (List.range (endsU x).length).flatMap fun i => triRow (pairB (un i) x)

/-- One `true` per `true` of the witness. -/
def trues (w : List Bool) : List Bool := w.filter id

/-- The code of the number of centres. -/
def cntS (w : List Bool) : List Bool := dig (incB^[(trues w).length] []) ++ [false, true]

/-- Point `s` (`us = un s`) covers point `y` (`uy = un y`): `s` is a centre, and `s = y` or
`d(s, y) ≤ τ`. -/
def covers (us uy x w : List Bool) : Bool :=
  !(f1 (List.tail^[us.length] w)).isEmpty &&
    (decide (us = uy) ||
      !(leF (if us.length < uy.length then entryS us uy x else entryS uy us x)
        (headI (dropI x))).isEmpty)

/-- On `pairB (un s) (pairB (un y) (pairB x w))`. -/
def covRow (z : List Bool) : List Bool :=
  bflag (covers (unpairB z).1 (unpairB (unpairB z).2).1
    (unpairB (unpairB (unpairB z).2).2).1 (unpairB (unpairB (unpairB z).2).2).2)

/-- On `pairB (un y) (pairB x w)`: nonempty when no point covers `y`. -/
def uncov (z : List Bool) : List Bool :=
  bflag ((List.range (endsU (unpairB (unpairB z).2).1).length).flatMap
    (fun s => covRow (pairB (un s) z))).isEmpty

/-- The uncovered points (empty when the centres dominate). -/
def uncovAll (x w : List Bool) : List Bool :=
  (List.range (endsU x).length).flatMap fun y => uncov (pairB (un y) (pairB x w))

/-- The verifier. -/
def CV (p : List Bool × List Bool) : Bool :=
  wfI p.1 && (triBad p.1).isEmpty && !(leF (cntS p.2) (headI p.1)).isEmpty &&
    (uncovAll p.1 p.2).isEmpty

end ClustNP
