import ClustNP.Defs
import RadiusClustering.PEqualNP.ItemGadget

/-!
# The reduction SAT → CLUST, as string functions

On the encoding `x` of a formula `φ` (pequalnp's `encodeCNF`), `red x` writes the instance
`itemInst φ` of `ItemGadget.lean`: `k` = the number of items, `τ = 1`, and the upper triangle of
the item gadget's dissimilarity (`1` on an edge, `2` otherwise). Vertex `i` is block `i / 3`,
role `i % 3`. On a string that encodes no formula, `red x = []`, which is not in CLUST.
-/

namespace ClustNP

open PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV
open PEqualNP.Library.SearchHelpers.S2D (incB dig)

/-! ### Items and vertices -/

/-- One `true` per item, i.e. per pair `[false, _]`. -/
def itemsU : List Bool → List Bool
  | false :: _ :: r => true :: itemsU r
  | _ :: _ :: r => itemsU r
  | _ => []

/-- `un (3 L)`, `L` the number of items: the vertices. -/
def vertsU (x : List Bool) : List Bool := itemsU x ++ itemsU x ++ itemsU x

/-- The block of vertex `|u|`. -/
def div3 (u : List Bool) : List Bool := un (u.length / 3)

/-- Role `0` (the true vertex). -/
def isR0 (u : List Bool) : Bool := decide (u.length % 3 = 0)

/-- Role `2` (third vertex, or clause vertex). -/
def isR2 (u : List Bool) : Bool := decide (u.length % 3 = 2)

/-- The string from item number `|up|` on. -/
def restAt (up x : List Bool) : List Bool := dropI^[up.length] x

/-- Item number `|up|` is an end of clause. -/
def endAt (up x : List Bool) : Bool := isEnd (restAt up x)

/-- The variable code of item number `|up|` (empty for an end of clause). -/
def varAt (up x : List Bool) : List Bool := (headI (restAt up x)).tail.tail

/-! ### Representatives and clause segments -/

/-- On `pairB (un q) (pairB up x)`: item `q` has the variable of item `|up|`. -/
def sameVar (z : List Bool) : List Bool :=
  bflag (decide (varAt (unpairB z).1 (unpairB (unpairB z).2).2 =
    varAt (unpairB (unpairB z).2).1 (unpairB (unpairB z).2).2))

/-- Item `|up|` is a literal and no earlier item has its variable. -/
def repAt (up x : List Bool) : Bool :=
  !endAt up x &&
    ((List.range up.length).flatMap fun q => sameVar (pairB (un q) (pairB up x))).isEmpty

/-- On `pairB (un r) (pairB up (pairB lit x))`: item `r` is `lit`, in the clause closed at
`|up|` (as many ends from `r` on as from `|up|` on). -/
def segHit (z : List Bool) : List Bool :=
  let r := (unpairB z).1
  let up := (unpairB (unpairB z).2).1
  let lit := (unpairB (unpairB (unpairB z).2).2).1
  let x := (unpairB (unpairB (unpairB z).2).2).2
  bflag (decide (headI (restAt r x) = lit) &&
    decide (endsU (restAt r x) = endsU (restAt up x)))

/-- The literal `lit` occurs in the clause closed by item `|up|`. -/
def segAt (up lit x : List Bool) : Bool :=
  !((List.range up.length).flatMap fun r => segHit (pairB (un r) (pairB up (pairB lit x)))).isEmpty

/-! ### Adjacency and rows -/

/-- The cross-block edge from the literal vertex `|ui|` to the clause vertex `|uj|`. -/
def crossAt (ui uj x : List Bool) : Bool :=
  !isR2 ui && isR2 uj && endAt (div3 uj) x && repAt (div3 ui) x &&
    segAt (div3 uj) (true :: isR0 ui :: varAt (div3 ui) x) x

/-- Vertices `|ui|` and `|uj|` are adjacent (for `|ui| ≠ |uj|`). -/
def adjAt (ui uj x : List Bool) : Bool :=
  if div3 ui = div3 uj then (!isR2 ui && !isR2 uj) || !endAt (div3 ui) x
  else crossAt ui uj x || crossAt uj ui x

/-- The code of `d(i, j)`: `1` on an edge, `2` otherwise. -/
def entryAt (ui uj x : List Bool) : List Bool :=
  sel (bflag (adjAt ui uj x)) [true, false, true, true, false, true] [true, true, false, true]

/-- On `pairB (un j') (pairB (un i) x)`: the code of `d(i, i + 1 + j')`. -/
def cell (z : List Bool) : List Bool :=
  entryAt (unpairB (unpairB z).2).1 ((unpairB (unpairB z).2).1 ++ true :: (unpairB z).1)
    (unpairB (unpairB z).2).2

/-- On `pairB (un i) x`: row `i` of the triangle. -/
def rowAt (z : List Bool) : List Bool :=
  ((List.range (List.tail^[((unpairB z).1).length + 1] (vertsU (unpairB z).2)).length).flatMap
    fun j => cell (pairB (un j) z)) ++ [false, false]

/-- All the rows. -/
def rowsOf (x : List Bool) : List Bool :=
  (List.range (vertsU x).length).flatMap fun i => rowAt (pairB (un i) x)

/-- **The reduction.** -/
def red (x : List Bool) : List Bool :=
  sel (bflag (wfB x)) []
    (dig (incB^[(itemsU x).length] []) ++ [false, true] ++ [true, true, false, true] ++ rowsOf x)

end ClustNP
