import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Basic definitions

Threshold graph, dominating sets, valid radius-constrained clusterings, and the dissimilarity
built from a graph. Paper/Lean choices: `docs/cadrage.md` §2–3.
-/

namespace RadiusClustering

variable {X α : Type*}

/-- Dissimilarity (Def. 1.2): zero on the diagonal, non-negative, symmetric. -/
structure IsDissimilarity [LE α] [Zero α] (d : X → X → α) : Prop where
  self : ∀ x, d x x = 0
  nonneg : ∀ x y, 0 ≤ d x y
  symm : ∀ x y, d x y = d y x

/-- Threshold graph `G_τ`: distinct `x`, `y` are adjacent iff `d x y ≤ τ` or `d y x ≤ τ`. -/
def thresholdGraph [LE α] (d : X → X → α) (τ : α) : SimpleGraph X :=
  SimpleGraph.fromRel fun x y => d x y ≤ τ

/-- `S` dominates `G`: every vertex is in `S` or adjacent to a vertex of `S` (Def. 1.20). -/
def IsDominating {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v, v ∈ S ∨ ∃ s ∈ S, G.Adj s v

/-- Every non-empty cluster of `f` has a centre inside it at dissimilarity `≤ τ` from all of its
points (Def. 1.10, 1.11). Clusters are the non-empty fibres of `f`; unused labels are allowed,
so this reads "a partition into at most `k` clusters". -/
def IsValidClustering [LE α] {k : ℕ} (d : X → X → α) (τ : α) (f : X → Fin k) : Prop :=
  ∀ y, ∃ c, f c = f y ∧ ∀ z, f z = f y → d c z ≤ τ

/-- `f` is derived from the centres `S` as in the proof of Th. 3.1: distinct centres get distinct
labels, and every other point gets the label of a nearest centre (ties broken arbitrarily). -/
def IsDerivedFrom [LE α] {k : ℕ} (d : X → X → α) (S : Finset X) (f : X → Fin k) : Prop :=
  Set.InjOn f S ∧ ∀ x ∉ S, ∃ c ∈ S, f x = f c ∧ ∀ c' ∈ S, d x c ≤ d x c'

/-- Dissimilarity of Th. 3.1 (part 2): `0` on the diagonal, `1` on edges, `2` otherwise. -/
def graphDissim {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : ℕ :=
  if u = v then 0 else if G.Adj u v then 1 else 2

end RadiusClustering
