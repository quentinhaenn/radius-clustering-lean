import RadiusClustering.Basic

/-!
# Order invariance: only the order of the values of `d` matters (ℝ → ℕ)
-/

namespace RadiusClustering

variable {X α β : Type*} [LinearOrder α] [LinearOrder β]

-- `hd`, `hτ` kept for uniformity with the reviewed statements (`docs/cadrage.md` §7).
set_option linter.unusedVariables false in
/-- Applying a strictly increasing `φ` to `d` and `τ` keeps the same valid clusterings. -/
theorem isValidClustering_comp_strictMono [Zero α] (φ : α → β) (hφ : StrictMono φ)
    (d : X → X → α) (hd : IsDissimilarity d) (τ : α) (hτ : 0 ≤ τ) {k : ℕ} (f : X → Fin k) :
    IsValidClustering (fun x y => φ (d x y)) (φ τ) f ↔ IsValidClustering d τ f := by
  simp only [IsValidClustering, hφ.le_iff_le]

-- `hd`, `hτ` kept for uniformity with the reviewed statements (`docs/cadrage.md` §7).
set_option linter.unusedVariables false in
/-- Applying a strictly increasing `φ` to `d` and `τ` keeps the same threshold graph. -/
theorem thresholdGraph_comp_strictMono [Zero α] (φ : α → β) (hφ : StrictMono φ)
    (d : X → X → α) (hd : IsDissimilarity d) (τ : α) (hτ : 0 ≤ τ) :
    thresholdGraph (fun x y => φ (d x y)) (φ τ) = thresholdGraph d τ := by
  ext u v
  simp [thresholdGraph, hφ.le_iff_le]

/-- **Order invariance.** Every instance `(X, d, τ)` has an ℕ-valued copy `(X, d', τ')` with the
same valid clusterings and the same threshold graph; `d'` is still a dissimilarity. -/
theorem exists_nat_copy [Fintype X] [Zero α] (d : X → X → α) (hd : IsDissimilarity d)
    (τ : α) (hτ : 0 ≤ τ) :
    ∃ (d' : X → X → ℕ) (τ' : ℕ), IsDissimilarity d' ∧
      (∀ (k : ℕ) (f : X → Fin k), IsValidClustering d' τ' f ↔ IsValidClustering d τ f) ∧
      thresholdGraph d' τ' = thresholdGraph d τ := by
  classical
  let V : Finset α := insert τ (Finset.univ.image fun p : X × X => d p.1 p.2)
  let φ : α → ℕ := fun a => (V.filter (· < a)).card
  have hφ : ∀ a ∈ V, ∀ b ∈ V, φ a ≤ φ b ↔ a ≤ b := by
    intro a ha b hb
    constructor
    · intro h
      by_contra hba
      rw [not_le] at hba
      have hsub : V.filter (· < b) ⊂ V.filter (· < a) := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨fun x hx => ?_, fun heq => ?_⟩
        · rw [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, hx.2.trans hba⟩
        · have hbmem : b ∈ V.filter (· < a) := Finset.mem_filter.2 ⟨hb, hba⟩
          rw [← heq] at hbmem
          exact lt_irrefl b (Finset.mem_filter.1 hbmem).2
      have := Finset.card_lt_card hsub
      simp only [φ] at h
      omega
    · intro h
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, lt_of_lt_of_le hx.2 h⟩
  have hdV : ∀ x y, d x y ∈ V := fun x y =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ (x, y)))
  have hτV : τ ∈ V := Finset.mem_insert_self _ _
  have hle : ∀ x y, φ (d x y) ≤ φ τ ↔ d x y ≤ τ := fun x y => hφ _ (hdV x y) _ hτV
  have hφ0 : φ 0 = 0 := by
    simp only [φ]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a ha
    rw [not_lt]
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact hτ
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 ha
      exact hd.nonneg _ _
  refine ⟨fun x y => φ (d x y), φ τ, ⟨fun x => ?_, fun _ _ => Nat.zero_le _, fun x y => ?_⟩,
    fun k f => ?_, ?_⟩
  · show φ (d x x) = 0
    rw [hd.self x]
    exact hφ0
  · show φ (d x y) = φ (d y x)
    rw [hd.symm x y]
  · simp only [IsValidClustering, hle]
  · ext u v
    simp only [thresholdGraph, SimpleGraph.fromRel_adj, hle]

end RadiusClustering
