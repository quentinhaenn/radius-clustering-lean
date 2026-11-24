import RadiusClustering.Basic

/-!
# T2: from a graph to a clustering instance (Th. 3.1, part 2)
-/

namespace RadiusClustering

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **T2 (i).** Thresholding `graphDissim G` at `1` gives back `G`. -/
theorem thresholdGraph_graphDissim : thresholdGraph (graphDissim G) 1 = G := by
  sorry

/-- **T2 (ii).** `graphDissim G` is a dissimilarity (Def. 1.2). -/
theorem isDissimilarity_graphDissim : IsDissimilarity (graphDissim G) := by
  sorry

/-- **T2 (iii).** `G` has a dominating set of size `≤ k` iff its vertices split into at most `k`
clusters of radius `≤ 1` for `graphDissim G`. -/
theorem exists_dominating_iff_exists_validClustering_graphDissim (k : ℕ) :
    (∃ S : Finset V, S.card ≤ k ∧ IsDominating G S) ↔
      ∃ f : V → Fin k, IsValidClustering (graphDissim G) 1 f := by
  sorry

end RadiusClustering
