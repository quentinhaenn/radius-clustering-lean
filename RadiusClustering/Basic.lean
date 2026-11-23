import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Basic definitions

Threshold graph, dominating sets, valid radius-constrained clusterings, and the dissimilarity
built from a graph. Paper/Lean choices: `docs/cadrage.md` §2–3.
-/

namespace RadiusClustering

variable {X α : Type*}

/-- Threshold graph `G_τ`: distinct `x`, `y` are adjacent iff `d x y ≤ τ` or `d y x ≤ τ`. -/
def thresholdGraph [LE α] (d : X → X → α) (τ : α) : SimpleGraph X :=
  SimpleGraph.fromRel fun x y => d x y ≤ τ

/-- `S` dominates `G`: every vertex is in `S` or adjacent to a vertex of `S` (Def. 1.20). -/
def IsDominating {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v, v ∈ S ∨ ∃ s ∈ S, G.Adj s v

/-- Every non-empty cluster of `f` has a centre inside it at dissimilarity `≤ τ` from all of its
points (Def. 1.10, 1.11). Labels in `Fin k`, empty clusters allowed: "at most `k` clusters". -/
def IsValidClustering [LE α] {k : ℕ} (d : X → X → α) (τ : α) (f : X → Fin k) : Prop :=
  ∀ y, ∃ c, f c = f y ∧ ∀ z, f z = f y → d c z ≤ τ

/-- Dissimilarity of Th. 3.1 (part 2): `0` on the diagonal, `1` on edges, `2` otherwise. -/
def graphDissim {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : ℕ :=
  if u = v then 0 else if G.Adj u v then 1 else 2

end RadiusClustering
