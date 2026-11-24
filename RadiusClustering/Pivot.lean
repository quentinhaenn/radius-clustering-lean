import RadiusClustering.Basic

/-!
# T3a: clustering into at most `k` clusters ⇔ dominating set of size at most `k`
-/

namespace RadiusClustering

/-- **T3a.** `X` splits into at most `k` clusters of radius `≤ τ` iff the threshold graph `G_τ`
has a dominating set of size `≤ k`. -/
theorem exists_validClustering_iff_exists_dominating
    {X α : Type*} [Fintype X] [LinearOrder α] [Zero α]
    (d : X → X → α) (τ : α)
    (hd : IsDissimilarity d) (hτ : 0 ≤ τ) (k : ℕ) :
    (∃ f : X → Fin k, IsValidClustering d τ f) ↔
      ∃ S : Finset X, S.card ≤ k ∧ IsDominating (thresholdGraph d τ) S := by
  sorry

/-- **T1** (Th. 3.1, optimisation form). `k` is the minimum number of clusters of radius `≤ τ`
iff `k` is the size of a minimum dominating set of `G_τ`. -/
theorem minClusters_iff_minDominating
    {X α : Type*} [Fintype X] [LinearOrder α] [Zero α]
    (d : X → X → α) (τ : α)
    (hd : IsDissimilarity d) (hτ : 0 ≤ τ) (k : ℕ) :
    ((∃ f : X → Fin k, IsValidClustering d τ f) ∧
        ∀ m < k, ¬ ∃ f : X → Fin m, IsValidClustering d τ f) ↔
      ((∃ S : Finset X, S.card = k ∧ IsDominating (thresholdGraph d τ) S) ∧
        ∀ S : Finset X, IsDominating (thresholdGraph d τ) S → k ≤ S.card) := by
  sorry

/-- **T1c** (existence). A dominating set `S` always has a partition derived from it, with `|S|`
labels. -/
theorem exists_isDerivedFrom
    {X α : Type*} [Fintype X] [LinearOrder α] [Zero α]
    (d : X → X → α) (τ : α) (hd : IsDissimilarity d) (hτ : 0 ≤ τ)
    (S : Finset X) (hS : IsDominating (thresholdGraph d τ) S) :
    ∃ f : X → Fin S.card, IsDerivedFrom d S f := by
  sorry

/-- **T1c** (Th. 3.1, constructive form). The partition derived from a minimum dominating set of
`G_τ` is valid, has exactly `|S|` clusters, and no valid partition has fewer. -/
theorem isDerivedFrom_minDominating
    {X α : Type*} [Fintype X] [LinearOrder α] [Zero α]
    (d : X → X → α) (τ : α)
    (hd : IsDissimilarity d) (hτ : 0 ≤ τ) (S : Finset X)
    (hS : IsDominating (thresholdGraph d τ) S)
    (hmin : ∀ S' : Finset X, IsDominating (thresholdGraph d τ) S' → S.card ≤ S'.card)
    {k : ℕ} (f : X → Fin k) (hf : IsDerivedFrom d S f) :
    IsValidClustering d τ f ∧ (Finset.univ.image f).card = S.card ∧
      ∀ m < S.card, ¬ ∃ g : X → Fin m, IsValidClustering d τ g := by
  sorry

end RadiusClustering
