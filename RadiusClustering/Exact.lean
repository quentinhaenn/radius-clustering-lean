import RadiusClustering.Pivot

/-!
# T3b: "exactly `k`" versus "at most `k`" clusters
-/

namespace RadiusClustering

variable {X α : Type*} [Fintype X] [LinearOrder α] [Zero α]

/-- **T3b.** For `k ≤ |X|`, a valid clustering with exactly `k` non-empty clusters (surjective `f`)
exists iff a valid clustering into at most `k` clusters exists. -/
theorem exists_surjective_validClustering_iff
    (d : X → X → α) (τ : α) (hd : IsDissimilarity d) (hτ : 0 ≤ τ)
    {k : ℕ} (hk : k ≤ Fintype.card X) :
    (∃ f : X → Fin k, Function.Surjective f ∧ IsValidClustering d τ f) ↔
      ∃ f : X → Fin k, IsValidClustering d τ f := by
  sorry

/-- Edge case `k > |X|`: no clustering has exactly `k` non-empty clusters. -/
theorem not_surjective_of_card_lt {k : ℕ} (hk : Fintype.card X < k) (f : X → Fin k) :
    ¬ Function.Surjective f := by
  sorry

/-- **T3b + T3a.** For `k ≤ |X|`: exactly `k` clusters of radius `≤ τ` iff `G_τ` has a
dominating set of size `≤ k`. -/
theorem exists_surjective_validClustering_iff_exists_dominating
    (d : X → X → α) (τ : α)
    (hd : IsDissimilarity d) (hτ : 0 ≤ τ)
    {k : ℕ} (hk : k ≤ Fintype.card X) :
    (∃ f : X → Fin k, Function.Surjective f ∧ IsValidClustering d τ f) ↔
      ∃ S : Finset X, S.card ≤ k ∧ IsDominating (thresholdGraph d τ) S := by
  sorry

end RadiusClustering
