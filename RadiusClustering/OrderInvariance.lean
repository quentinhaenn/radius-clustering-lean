import RadiusClustering.Basic

/-!
# Order invariance: only the order of the values of `d` matters (ℝ → ℕ)
-/

namespace RadiusClustering

variable {X α β : Type*} [LinearOrder α] [LinearOrder β]

/-- Applying a strictly increasing `φ` to `d` and `τ` keeps the same valid clusterings. -/
theorem isValidClustering_comp_strictMono (φ : α → β) (hφ : StrictMono φ)
    (d : X → X → α) (τ : α) {k : ℕ} (f : X → Fin k) :
    IsValidClustering (fun x y => φ (d x y)) (φ τ) f ↔ IsValidClustering d τ f := by
  sorry

/-- Applying a strictly increasing `φ` to `d` and `τ` keeps the same threshold graph. -/
theorem thresholdGraph_comp_strictMono (φ : α → β) (hφ : StrictMono φ)
    (d : X → X → α) (τ : α) :
    thresholdGraph (fun x y => φ (d x y)) (φ τ) = thresholdGraph d τ := by
  sorry

/-- **Order invariance.** Every instance `(X, d, τ)` has an ℕ-valued copy `(X, d', τ')` with the
same valid clusterings and the same threshold graph; `d'` is still a dissimilarity. -/
theorem exists_nat_copy [Fintype X] [Zero α] (d : X → X → α) (hd : IsDissimilarity d)
    (τ : α) (hτ : 0 ≤ τ) :
    ∃ (d' : X → X → ℕ) (τ' : ℕ), IsDissimilarity d' ∧
      (∀ (k : ℕ) (f : X → Fin k), IsValidClustering d' τ' f ↔ IsValidClustering d τ f) ∧
      thresholdGraph d' τ' = thresholdGraph d τ := by
  sorry

end RadiusClustering
