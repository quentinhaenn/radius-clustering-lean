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
    (hdiag : ∀ x, d x x = 0) (hsymm : ∀ x y, d x y = d y x) (hτ : 0 ≤ τ) (k : ℕ) :
    (∃ f : X → Fin k, IsValidClustering d τ f) ↔
      ∃ S : Finset X, S.card ≤ k ∧ IsDominating (thresholdGraph d τ) S := by
  sorry

end RadiusClustering
